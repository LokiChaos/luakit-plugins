-------------------------------------------------------------------------------
-- Advanced URI-based content filter v0.1.1a                                 --
--  Combines functionality of AdBlock via pattern-match based blocking,      --
--  domain/sub-domain matching white and black listing,                      --
--  a RequestPolicy-like rule system to default-deny 3rd-party requests      --
--  and rough per-domain file-type filtering based on URI patterns           --
--                                                                           --
-- Disclaimer: while this is intended to increase browser security and       --
-- help protect privacy, there is no guarntee.  Rely on it at your own risk! --
-------------------------------------------------------------------------------

local info = info
local pairs = pairs
local ipairs = ipairs
local assert = assert
local unpack = unpack
local type = type
local io = io
local os = os
local string = string
local table = table
local tostring = tostring
local tonumber = tonumber
local webview = webview
local window = window
local lousy = require("lousy")
local theme = require("theme")
local widget = widget
local util = lousy.util
local chrome = require("chrome")
local capi = { luakit = luakit , sqlite3 = sqlite3 }
local sql_escape = lousy.util.sql_escape
local add_binds, add_cmds = add_binds, add_cmds
local new_mode, menu_binds = new_mode, menu_binds
local lfs = require("lfs")
local setmetatable = setmetatable

-- Calls modifed adblock
--local adblock = require("plugins.adblock")

module("plugins.policy")

pdebug = function (...)
	if true then
		io.stdout:write(string.format(...) .. "\n")
	end
end

-- Settings Flags =============================================================
filtering = {
	-- Flag to accept all requests (disabled all blocking)
	acceptall = false,
	-- Flag to enable/disable AdBlock / Pattern-Based Blocking
	adblock = true,
	-- Flag to enable/disable additional scrutiny of 3rd-party requests
	requestpolicy = true,
	-- Flag to enable/disable file-type blocking policy
	typepolicy = true,
	-- Flag for whether a subdomain is treated as a 3rd party relative to other subdomains or master domain
	strictsubdomain = false
}

local policy_dir = capi.luakit.data_dir

-- A table to store data for navigation and resource requests
-- it has per-view instances, indexed via navto[v].fields
local navto = {}
setmetatable(navto, { __mode = "k" })

-- Below is the actual internals of the plugin, here be dragons ---------------
-------------------------------------------------------------------------------
-- Exception listing
local exlist = { white = {}, third = {white = {} } }

-- Makes the following more clear... eg: return codes and internal constants
-- allowing is zero so that reasons for denial can be communicated
local ALLOW = 0
local DENIED = { BLACKLIST = 1, ADBLOCK = 2, NO_WHITELIST = 3, BLACKLISTED_TP = 4 , BLOCKED_TYPE = 5 } 
local ANY_PARTY, THIRD_PARTY = 1, 2
local reasonstring = {"Blacklisted", "ABP", "CDR", "Blacklisted-CDR", "F-TYPE", "Other"}

-- sqlite command stings
local create_tables = [[
PRAGMA synchronous = OFF;
PRAGMA secure_delete = 1;
CREATE TABLE IF NOT EXISTS whitelist (
	id INTEGER PRIMARY KEY,
	domain TEXT UNIQUE
);
CREATE TABLE IF NOT EXISTS blacklist (
	id INTEGER PRIMARY KEY,
	domain TEXT UNIQUE
);
CREATE TABLE IF NOT EXISTS tp_whitelist (
	id INTEGER PRIMARY KEY,
	domain TEXT,
	rdomain TEXT

);
CREATE TABLE IF NOT EXISTS tp_blacklist (
	id INTEGER PRIMARY KEY,
	domain TEXT,
	rdomain TEXT
);
]]

local sql_format = {
	match_list             = "SELECT * FROM %slist WHERE domain == %s;",
	add_list               = "INSERT INTO %slist VALUES (NULL, %s);",
	remove_list            = "DELETE FROM %slist WHERE domain == %s;",
	match_tp_list          = "SELECT * FROM tp_%slist WHERE domain == %s and rdomain == %s;",
	add_tp_list            = "INSERT INTO tp_%slist VALUES (NULL, %s, %s);",
	remove_tp_list_domain  = "DELETE FROM tp_%slist WHERE domain == %s;",
	remove_tp_list_rdomain = "DELETE FROM tp_%slist WHERE rdomain == %s;",
	remove_tp_list_exact   = "DELETE FROM tp_%slist WHERE domain == %s and rdomain == %s;",
}

-- Open or create & initiaze dbi
initalize_rpdb = function()
	if rpdb then return end
	rpdb = capi.sqlite3{ filename = policy_dir .. "/policy.db" }
	rpdb:exec(create_tables)
end

-- Helper functions that perform various utility functions ========================

-- Attempt to parse a uri for the extension of the requested file
-- return file extension in lower case or "NONE" if no extension
local getextension = function (uri)
	if uri then
		local puri = lousy.uri.parse(uri)
		local ext = string.match(puri and puri.path or "", "%.([a-zA-Z0-9]-)$")
		return ext and string.lower(ext) or "NONE"
	end
	return "NONE"
end

-- Returns the (probable_main domain.tld or domain.2tld.tld) of the given host
-- Eg: api.google.com    > google.com
--     hats.amazon.co.jp > amazon.co.jp
-- XXX: This is _not_ perfect, but it should handle the most common domain cases.
-- There is no proper way to handle this with just glob-matching (or even regex)
local getdomain = function (host)
	if host then
		local bits = util.table.reverse(util.string.split(host, "%.") or {})
		-- Host is an IP, domain == IP
		if #bits < 3 or (bits[1] and string.match(bits[1], "^%d+$")) then
			return host
		else
			local phost = bits[2] .. "." .. bits[1]
			if string.len(phost) < 6 then
				return bits[3] .. "." .. phost
			else
				return phost
			end
		end
	end
end

-- Check if query is domain or a subdomain of host
local subdomainmatch = function(host, query)
	if host == query then
		return true
	else
		local abits = util.string.split(string.reverse(host) or "", "%.")
		local bbits = util.string.split(string.reverse(query) or "", "%.")
		-- If host is an IP abort, eg: 10.8.4.1 is not a subdomain of 8.4.1
		if abits[1] and string.match(abits[1], "^%d+$") then return false end
		for i,s in ipairs(abits) do
			if s ~= bbits[i] then
				return false
			end
		end
		return true
	end
end

-- Checks domains for a match
local domainmatch = function (a, b)
	-- If main uri (a) is nil, then it is always "first party"
	-- If a == b then they are the same domain
	-- Otherwise do a match score and make a fuzzy match
	if not a or a == b then
		return true
	elseif not filtering.strictsubdomain then
		local abits = util.string.split(string.reverse(a) or "", "%.")
		local bbits = util.string.split(string.reverse(b) or "", "%.")
		local matching = 0
		-- If an IP, don't do partial matches
		if abits[1] and string.match(abits[1], "^%d+$") then
			return false
		end
		for i,s in ipairs(abits) do
			if s == bbits[i] then
				matching = matching + 1
			else
				break
			end
		end
		-- XXX: again, this is a dirty hack to deal with 2 part "tlds" eg: .co.jp
		local needed_match = 1 + (string.len(abits[1] or "123") < 3 and string.len(abits[2] or "123") < 3 and 1 or 0)
		if matching > needed_match then
			return true
		end
	end
	return false
end

-- Returns whether or not rhost is whitelisted
local islisted = function (host, rhost, typ, party)
	if party == THIRD_PARTY then
		local host_bits = util.table.reverse(util.string.split(host or "", "%.") or {})
		local phost = host
		local n = 3
		-- Check for long hosts and non IPs
		if host and #host_bits > 2 and not string.match(host_bits[1], "^%d+$") then	
			phost = host_bits[2] .. "." .. host_bits[1]
			if string.len(phost) < 5 then
				-- XXX again, same dirty trick to deal with .co.jp "tlds"
				phost = host_bits[3] .. "." .. phost
				n = 4
			end
		end
		-- Make list to match rhost against
		local list = rpdb:exec(string.format("SELECT * FROM tp_%slist WHERE domain = %s;", typ, sql_escape("all")))
		local tlist = exlist.third.white["all"]
			repeat
				local rows = rpdb:exec(string.format("SELECT * FROM tp_%slist WHERE domain = %s;", typ, sql_escape(phost)))
				list = util.table.join(list, rows or {})
				if typ == "white" then
					tlist = util.table.join(tlist, exlist.third.white[phost] or {})
				end
				phost = (host_bits[n] or "").. "." .. phost
				n = n + 1
			until n > #host_bits + 1
			for _,v in pairs(list) do
				if subdomainmatch(v.rdomain, rhost) or v.rdomain == "all" then
					return true
				end
			end
			-- Only check exceptions if checking a whitelist
			if typ == "white" then
				for k,v in pairs(tlist) do
					if subdomainmatch(v, rhost) or v == "all" then
						return true
					end
				end
			end
		return false
	else
		local list = rpdb:exec(string.format("SELECT * FROM %slist;", typ))
		for _,v in pairs(list) do
			if subdomainmatch(v.domain, rhost) then
				return true;
			end
		end
		-- Only check exceptions if checking a whitelist
		if typ == "white" then
			for k,v in pairs(exlist.white) do
				if subdomainmatch(k, rhost) then
					return true;
				end
			end
		end
	end
	-- No match was found
	return false
end

-- Check Pattern list for matches to rules (aka AdBlocking)
local patternMatch = function (req)
	-- This checks that the AdBlock Module is loaded, and if so it calls the matching function
	-- I originally intended to re-implement this as part of this plugin, but I decided that
	-- it was better to just use a minimally modified version of the upstream AdBlock plugin
	if filtering.adblock and adblock and adblock.match then
		return not adblock.match(req, "none")
	end
	return false
end

-- Main logic checking if a request should be allowed or denied
local checkpolicy = function (host, requested, nav, firstnav)
	-- A request for a nil uri is denied (should never happen)
	if not requested then
		return DENIED.BLACKLIST
	end

	-- Should always accept these
	if string.match(requested, "about:blank") or filtering.acceptall then
		return ACCEPT
	end

	-- Get host from requested uri and file-type extension
	local rpuri = lousy.uri.parse(requested)
	local req = { host = string.lower(rpuri and rpuri.host or ""), ftype = getextension(requested) }

	-- webview.uri is nil for the first requests when loading a page (they are always first party)	
	local puri = lousy.uri.parse(host or "")
	host = puri and puri.host or req.host

	-- Blacklisting overrides whitelist
	if islisted(nil, req.host, "black", ANY_PARTY) then
		return DENIED.BLACKLIST
	end
	
	-- Check if requested domain is whitelisted
	local wlisted = islisted(nil, req.host, "white", ANY_PARTY)

	-- Whitelisting overrides AdBlocking/Pattern Block
	if not wlisted and filtering.adblock then
		-- If AdBlock / Pattern matching is enabled, check if requested uri matches and should be blocked
		if patternMatch(requested) then
			return DENIED.ADBLOCK
		end
	end

	-- If RequestPolicy is disabled or this is a first party request only type-blocking is checked
	-- If this is a a navigation request or the first request post-navigation, relax CDR, we likely clicked on a link
	-- data: uri's are not cross-domain, however we might want to check those with file filtering
	if nav or firstnav or not filtering.requestpolicy or domainmatch(host, req.host) or string.match(requested, "^data:")then
		-- TODO: file-type blocking
		return ACCEPT
	else
		-- Check if this domain is blacklised for ALL 3rd-party requests -OR-
		-- blacklisted for 3rd party requests for the main domain
		if islisted(host, req.host, "black", THIRD_PARTY) then
			return DENIED.BLACKLISTED_TP
		end

		-- If requested host is whitelisted universally or for this host for this third party, set to accept
		local wlistedtp = islisted(host, req.host, "white", THIRD_PARTY)
		if not wlistedtp then
			return DENIED.NO_WHITELIST
		end
		-- TODO: file-type blocking that overrides whitelisted 3rd party requrests
		return ACCEPT
	end
end

-- Make a table of request's hosts and keep a count of accepted and denied requests
local concatRes = function (l, uri, r)
	if uri then
		local puri = lousy.uri.parse(uri)
		if puri and puri.host then
			-- If the host doesn't have a table yet, add it
			if not l[puri.host] then
				l[puri.host] = { accept = 0, deny = 0 , reasons = {} }
			end
			-- Increment counter (s)
			if not r then
				l[puri.host].accept = 1 + l[puri.host].accept
			else
				l[puri.host].deny = 1 + l[puri.host].deny
				-- TODO get make this not so hacky ??
				l[puri.host].reasons[reasonstring[r]] = (l[puri.host].reasons[reasonstring[r]] or 0) + 1
			end
		end
	end
end


-- XXX For Debugging only, REMOVE
local filterDEBUG = function (main_uri, request, nav, po, first)
	local puri = lousy.uri.parse(main_uri or "")
	local host = puri and puri.host or "NONE"
	pdebug("policy: %s request made by %s", nav and "navigation" or "resource", host or "NONE")

	if not po then
		pdebug("policy: accepted request for '%s'", request)
	elseif po == DENIED.BLACKLIST then
		pdebug("policy: denied request [Blacklisted Domain] for '%s'", request)
	elseif po == DENIED.ADBLOCK then
		pdebug("policy: denied request [Pattern Match] for '%s'", request)
	elseif po == DENIED.NO_WHITELIST then
		pdebug("policy: denied request [Non-Whitelisted CDR] for '%s'", request)
	elseif po == DENIED.BLACKLIST_TP then
		pdebug("policy: denied request [Blacklisted CDR] for '%s'", request)
	elseif po == DENIED.BLOCKED_TYPE then
		pdebug("policy: denied request [Blocked File-type] for '%s'", request)
	else
		pdebug("policy: denied request [Unknown Reason] for '%s'", request)	
	end 
end

-- Connect signals to all webview widgets on creation
-- TODO check robustness of the firstnav system
webview.init_funcs.policu_signals = function (view, w)
    view:add_signal("navigation-request", 
					function (v, uri)
						-- Check if request should be accepted or denied
						local r = checkpolicy(v.uri, uri, true , false)

						-- if navto[v] does not exist set to empty table
						navto[v] = navto[v] or {}

						-- Only do the following if request was accepted (r = 0)
						if not r then
							-- Set temp navigation uri to the requested uri
							navto[v].uri = uri
							-- Make an empty request table if one does not exist	
							navto[v].res = navto[v].res or {}
							-- Add request to the resource request table
							--concatRes(navto[v].res, uri, r) -- TODO I don't think this is needed?
							-- XXX  "bug-fix" ensures uri bar gets updated on clicking intra-page links
							w:update_uri()
						elseif r == DENIED.BLACKLIST then
							w:error("Policy: Blacklisted domain '" .. uri .. "'")
						end
						-- Hack to get luakit;// pages to load
						local puri = lousy.uri.parse(uri or "")
						if puri and puri.scheme == "luakit" then
						else
							-- remember, accept = 0
							return not r
						end				
					end)
 
    view:add_signal("resource-request-starting",
					function (v, uri)
						-- Check if request should be accepted or denied
						local r = checkpolicy(navto[v].uri or v.uri, uri, false, (navto[v] or {}).first)

						-- if w.navto[v] does not exist set to empty table
						navto[v] = navto[v] or {}
						-- Clear temp navigation uri
						navto[v].uri = nil
						-- Clear first flag
						navto[v].first = false
						-- Add the request to the request table
						concatRes(navto[v].res, uri, r)
						-- Hack to get luakit;// pages to load
						local puri = lousy.uri.parse(uri or "")
						if puri and puri.scheme == "luakit" then
						else
							--remember, accept = 0
							return not r
						end
					end)

    view:add_signal("load-status",
					function (v, status)
						--pdebug(("policy: load-status signal uri = " .. (v.uri or "") .. "status = " .. status) or "policy: load-status ???")
						navto[v] = navto[v] or {}
						if status == "provisional" then
							-- Resets Resource requests
							navto[v].res = {}
							navto[v].first = true
						elseif status == "committed" then
							navto[v].first = false
						end
        			end)
end

-- TODO - All the chrome stuff...
-- luakit://policy/help			help page, lists commands and explains how to use plugin
-- luakit://policy				displys settings status and links to other pages
-- luakit://policy/whitelist	list of whitelisted domains (button to remove, search, and add new entries)
-- luakit://policy/blacklist	list of blacklisted domains (button to remove, search, and add new entries)
-- luakit://policy/cdr/whitelist  list of CDR whitelist entries (")
-- luakit://policy/cdr/blacklist  list of CDR blacklist entries (")
-- luakit://policy/adblock		  redirects to luakit://adblock 

load = function ()
	-- Load the db with the white/black lists
	initalize_rpdb()
end

-- Functions called by user commands ========================================== 
local togglestrings = {
	acceptall = "unconditional accepting of all requests.",
	adblock = "pattern-based blocking (aka AdBlock).",
	requestpolicy = "cross-domain request policy blocking.",
	typepolicy = "cross-domain file-type blocking",
	strictsubdomain = "strict matching for subdomains.",
}

local rp_setting = function (field, value, w)
	-- Check that field is a valid settings field
	if togglestrings[field] then
		-- Check is toggling or setting value
		if value == "toggle" then
			filtering[field] = not filtering[field]
		else
			filtering[field] = value
		end
		-- User feedback on what setting was changed and what it was changed to
		w:notify("Policy: " .. (value and "en" or "dis") .. "abled " .. togglestrings[field])
	end
	-- return validity of the setting
	return togglestrings[field] and true
end

-- Add A host to the temporary exceptions table
local add_ab_exception = function(host, w)
	if not util.table.hasitem(exlist.white or {}, host) then
		table.insert(exlist.white, host)
		w:notify("Added an exception for '".. host .. "'")
	else
		w:error("Policy: '" .. host .. "' was already granted an exception.")
	end
end

local del_ab_exception = function(host, w)
	local i = util.table.hasitem(exlist.white or {}, host)
	if i then
		table.remove(exlist.white, i)
		w:notify("Removed exception for '".. host .. "'")
	else
		w:error("Policy: '" .. host .. "' had not been granted an exception.")
	end
end

local add_tp_exception = function(host, rhost, w)
	-- If host doesn't have a exception list entry, make an empty one
	if not exlist.third.white[host] then
		exlist.third.white[host] = {}
	end
	if not util.table.hasitem(exlist.third.white[host], rhost) then
		table.insert(exlist.third.white[host], rhost)
		w:notify("Added an exception for requests from '".. host .. "' to '" .. rhost .. "'")
	else
		w:error("Policy: '" .. rhost .. "' was already granted an exception.")
	end
end

local del_tp_exception = function(host, rhost, w)
	if exlist.third.white[host] then
		local i =  util.table.hasitem(exlist.third.white[host] or {}, rhost) 
		if i then
			table.remove(exlist.third.white[host], i)
			w:notify("Removed exception for requests from '".. host .. "' to '" .. rhost .. "'")
			return
		end
	end
	w:error("Policy: '" .. host .. " - " .. rhost .."' had not been granted an exception.")
end

-- Add host to domain white or black list
local add_list = function (host, typ, w)
	local row = rpdb:exec(string.format(sql_format.match_list, typ, sql_escape(host)))
	if row and row[1] then
		w:error("Policy: '" .. host .. "' is already " .. typ .. "listed")
	else
		rpdb:exec(string.format(sql_format.add_list, typ, sql_escape(host)))
		w:notify("Added '".. host .. "' to " .. typ .."list")
	end
end

local add_tp_list = function (host, rhost, typ, w)
	local row = rpdb:exec(string.format(sql_format.match_tp_list, typ, sql_escape(host), sql_escape(rhost)))
	if row and row[1] then
		w:error("Policy: '" .. host .. " - " .. rhost .. "' is already " .. typ .. "listed")
	else
		rpdb:exec(string.format(sql_format.add_tp_list, typ, sql_escape(host), sql_escape(rhost)))
		w:notify("Added '".. host .. " - " .. rhost .."' to " .. typ .."list")
	end
end

-- Remove host from domain white or black list
local del_list = function(host, typ, w)
	local row = rpdb:exec(string.format(sql_format.match_list, typ, sql_escape(host)))
	if row and row[1] then
		rpdb:exec(string.format(sql_format.remove_list, typ, sql_escape(host)))
		w:notify("Removed '".. host .. "' from " .. typ .."list")
	else
		w:error("Policy: '" .. host .. "' was not " .. typ .. "listed")
	end
end

local del_tp_list = function (host, rhost, typ, w)
	local row = rpdb:exec(string.format(sql_format.match_tp_list, typ, sql_escape(host), sql_escape(rhost)))
	if row and row[1] then
		rpdb:exec(string.format(sql_format.remove_tp_list_exact, typ, sql_escape(host), sql_escape(rhost)))
		w:notify("Removed '".. host .. " - " .. rhost .."' from " .. typ .."list")
	else
		w:error("Policy: '" .. host .. " - " .. rhost .. "' was not " .. typ .. "listed")
	end
end


-- Master user commands parser
local rp_command = function(command, w, a)
	a = string.lower(a or "")
	local args = util.string.split(util.string.strip(a or ""), " ")
	-- Attempt to get a host/rhost out of args
	local host  = args[1] and ((args[1] == "all" and "all") or (lousy.uri.parse(args[1]) or {}).host)
	local rhost = args[2] and ((args[2] == "all" and "all") or (lousy.uri.parse(args[2]) or {}).host)
		if command == "wl" or command == "whitelist" then
			if #args == 1 then
				if host then
					add_list(host, "white", w)
				else
					w:error("Policy: wl, Bad argument error. (" .. host .. ")")	
				end
			elseif #args == 2 then
				if host and rhost then
					add_tp_list(host, rhost, "white", w)
				else
					w:error("Policy: wl, Bad argument error. (" .. host .. ")")	
				end
			else
				w:error("Policy: wl, Wrong number of arguments!")
			end
		elseif command == "bl" or comamnd == "blacklist" then
			if #args == 1 then
				if host then
					add_list(host, "black", w)
				else
					w:error("Bad argument error. (" .. host .. ", " .. rhost ..")")	
				end
			elseif #args == 2 then
				if host and rhost then
					add_tp_list(host, rhost, "black", w)
				else
					w:error("Bad argument error. (" .. host .. ", " .. rhost ..")")	
				end
			else
				w:error("Wrong number of arguments!")
			end

		elseif command == "ex" or command == "exception" then
			if #args == 1 then
				if host then
					add_ab_exception(host, w)
				else
					w:error("Bad argument error. (" .. host .. ")")	
				end
			elseif #args == 2 then
				if host and rhost then
					add_tp_exception(host, rhost, w)
				else
					w:error("Bad argument error. (" .. host .. ", " .. rhost ..")")	
				end
			else
				w:error("Wrong number of arguments!")
			end
		elseif command == "wl!" or command == "whitelist!" then
			if #args == 1 then
				if host then
					del_list(host, "white", w)
				else
					w:error("Bad argument error. (" .. host .. ")")	
				end
			elseif #args == 2 then
				if host and rhost then
					del_tp_list(host, rhost, "white", w)
				else
					w:error("Bad argument error. (" .. host .. ", " .. rhost ..")")	
				end
			else
				w:error("Wrong number of arguments!")
			end
			-- Remove 
		elseif command == "bl!" or command == "blacklist!" then
			if #args == 1 then
				if host then
					del_list(host, "black", w)
				else
					w:error("Bad argument error. (" .. host .. ")")	
				end
			elseif #args == 2 then
				if host and rhost then
					del_tp_list(host, rhost, "black", w)
				else
					w:error("Bad argument error. (" .. host .. ", " .. rhost ..")")	
				end
			else
				w:error("Wrong number of arguments!")
			end
		elseif command == "ex!" or command == "exception!" then
			if #args == 1 then
				if host then
					del_ab_exception(host, w)
				else
					w:error("Bad argument error. (" .. host .. ")")	
				end
			elseif #args == 2 then
				if host and rhost then
					del_tp_exception(host, rhost, w)
				else
					w:error("Bad argument error. (" .. host .. ", " .. rhost ..")")	
				end
			else
				w:error("Wrong number of arguments!")
			end

		elseif command == "wl!!" or command == "whitelist!!" or
			   command == "wl-removeall" or command == "whitelist-removeall" then

		elseif command == "bl!!" or command == "blacklist!!" or
			   command == "bl-removeall" or command == "blacklist-removeall" then

		elseif command == "set" then
		-- Set request policy behaviors
			local val = not string.match(args[1], "!$")
			local set = string.match(args[1], "(.*)!$") or args[1]
			if not rp_setting(set, val, w) then
				w:error("Policy: set '" .. args[1] .. "' is not a valid setting. (adblock[!], requestpolicy[!], typepolicy[!], acceptall[!], strictsubdomain[!])")
			end
		elseif command == "clear" then
			-- Clear temp tables
			local listlen = #exlist.white
			for _,v in pairs(exlist.third.white) do
				for _,_ in pairs(v) do
					listlen = listlen + 1
				end
			end
			exlist.white = {}
			exlist.third.white = {}
			w:notify(string.format("Removed %d policy exceptions.", listlen))
		else
			w:error("Policy: '" .. command .. "' is not a valid request policy command!")
		end
end

-- Add commands ===============================================================
new_mode("policymenu", {
    enter = function (w)
        local afg = theme.rpolicy_active_menu_fg or theme.proxy_active_menu_fg
        local ifg = theme.rpolicy_inactive_menu_fg or theme.proxy_inactive_menu_fg
        local abg = theme.rpolicy_active_menu_bg or theme.proxy_active_menu_bg
        local ibg = theme.rpolicy_inactive_menu_bg or theme.proxy_inactive_menu_bg

		local template = ' Allowed: <span foreground = "#0f0">%2d</span>  Blocked: <span foreground = "#f00">%2d</span> %s'
		local reason = { start = "[Reason(s):", ends  = "]"}

		local main = (lousy.uri.parse(w.view.uri) or {}).host or "about:config"
        local rows = {}
		local main_row
        for host,pol in pairs(navto[w.view].res) do
			-- Generate a list of reason why requests were blocked
			local reasons = ""
			for k,_ in pairs(pol.reasons) do
				reasons = reasons .. (k and " ") .. k
			end
			local notcdr = domainmatch(main, host)
			if host == main then
				main_row = {
				" " .. host .. "", string.format(template, pol.accept ,pol.deny, ((reasons ~= "") and reason.start .. reasons .. reason.ends) or ""),
                host = host, pol = pol,
                fg = (notcdr and afg) or ifg,
                bg = ibg}
			else
	            table.insert(rows, (notcdr and 1) or #rows +1,
				{   " " .. host .. "", string.format(template, pol.accept ,pol.deny, ((reasons ~= "") and reason.start .. reasons .. reason.ends) or ""),
        	        host = host, pol = pol,
            	    fg = (notcdr and afg) or ifg,
                	bg = ibg,
	            })
			end
        end
		-- Add main host to top of the list
		if main_row then
			table.insert(rows, 1, main_row)
		end
		-- Add title row entry
		table.insert(rows, 1, { "Domains requested by " .. main, "Actions Taken", title = true })
        w.menu:build(rows)
        w:notify("Use j/k to move, Enter to select a host and open actions submeny, or h to open policy help (and full list of actions).", false)
    end,

    leave = function (w)
        w.menu:hide()
    end,
})

new_mode("policysubmenu", {
    enter = function (w)
        local afg = theme.rpolicy_active_menu_fg or theme.proxy_active_menu_fg
        local ifg = theme.rpolicy_inactive_menu_fg or theme.proxy_inactive_menu_fg
        local abg = theme.rpolicy_active_menu_bg or theme.proxy_active_menu_bg
        local ibg = theme.rpolicy_inactive_menu_bg or theme.proxy_inactive_menu_bg
		local host = navto[w.view].selectedhost or "REQ_HOST"
		local main = (lousy.uri.parse(w.view.uri or "") or {}).host or "HOST"
		-- TODO make this menu smart, and only have entried that are applicable
        local rows = {{ "Actions for " .. host , "Command", title = true }}

		-- plain whitelist/blacklist
		if (rpdb:exec(string.format(sql_format.match_list, "white", sql_escape(host))) or {})[1] then
			table.insert(rows,
					  { "Remove " .. host .. " from whitelist",
					   " :rp wl! " .. host,
					   host = host, main = main, cmd = "wl!",
					   fg = ifg, bg = ibg })
		else
			table.insert(rows,
					  { "Add " .. host .. " to whitelist",
					   " :rp wl " .. host,
					   host = host, main = main, cmd = "wl",
					   fg = ifg, bg = ibg })
		end
		if (rpdb:exec(string.format(sql_format.match_list, "black", sql_escape(host))) or {})[1] then
			table.insert(rows,
					  { "Remove " .. host .. " from blacklist",
					   " :rp bl! " .. host,
					   host = host, main = main, cmd = "bl!",
					   fg = ifg, bg = ibg })
		else
			table.insert(rows,
					  { "Add " .. host .. " to blacklist",
					   " :rp bl " .. host,
					   host = host, main = main, cmd = "bl",
					   fg = ifg, bg = ibg })
		end

	-- Sud-menu for the page's domain
	if host == main then
		if (rpdb:exec(string.format(sql_format.match_tp_list, "white", sql_escape("all"), sql_escape(host))) or {})[1] then
			table.insert(rows,
					  { "Revoke complete CDRs whitelisting from " .. main,
					   " :rp wl! " .. main .. " ALL",
					   host = "all", main = main, cmd = "wl!",
					   fg = ifg, bg = ibg })
		else
			table.insert(rows,
					  { "Allow all CDRs from " .. main,
					   " :rp wl " .. main .. " ALL",
					   host = "all", main = main, cmd = "wl",
					   fg = ifg, bg = ibg })
		end
		if (rpdb:exec(string.format(sql_format.match_tp_list, "black", sql_escape("all"), sql_escape(host))) or {})[1] then
			table.insert(rows,
					  { "Remove complete CDR blacklisting from " .. main,
					   " :rp bl! " .. main .. " ALL",
					   host = "all", main = main, cmd = "bl!",
					   fg = ifg, bg = ibg })
		else
			table.insert(rows,
					  { "Blacklist all CDRs for " .. main,
					   " :rp bl " .. main .. " ALL",
					   host = "all", main = main, cmd = "bl",
					   fg = ifg, bg = ibg })
		end
		if util.table.hasitem(exlist.white or {}, main) then
			table.insert(rows,
					  { "Remove temporarily whitelisting of " .. main,
					   " :rp ex! " .. main,
					   host = host, main = main, cmd = "ex!",
					   fg = ifg, bg = ibg })
		else
			table.insert(rows,
					  { "Temporarily whitelist " .. main,
					   " :rp ex " .. main,
					   host = host, main = main, cmd = "ex",
					   fg = ifg, bg = ibg })
		end
		if exlist.third.white[main] then
			--TODO remove temp tp whitelist all CDR
		else
			table.insert(rows,
					  { "Temporarily allow all CDRs from " .. main,
					   " :rp ex " .. main .. " ALL", 
					   host = "all", main = main, cmd = "ex",
					   fg = ifg, bg = ibg })
		end
	else
		if (rpdb:exec(string.format(sql_format.match_tp_list, "white", sql_escape(main), sql_escape(host))) or {})[1]then
			table.insert(rows,
					  { "Revoke the CDR whitelisting for this host from " .. main,
					   " :rp wl! " .. main .. " " .. host, 
					   host = host, main = main, cmd = "wl!",
					   fg = ifg, bg = ibg })
		else
			table.insert(rows,
					  { "Allow CDRs to this host from " .. main,
					   " :rp wl " .. main .. " " .. host, 
					   host = host, main = main, cmd = "wl",
					   fg = ifg, bg = ibg })
		end
		if (rpdb:exec(string.format(sql_format.match_tp_list, "black", sql_escape(main), sql_escape(host))) or {})[1]then
			table.insert(rows,
					  { "Remove the CDR blacklisting for this host from " .. main,
					   " :rp bl! " .. main .. " " .. host, 
					   host = host, main = main, cmd = "bl!",
					   fg = ifg, bg = ibg })
		else
			table.insert(rows,
					  { "Blacklist CDRs to this host from " .. main,
					   " :rp bl " .. main .. " " .. host, 
					   host = host, main = main, cmd = "bl",
					   fg = ifg, bg = ibg })
		end
		if (rpdb:exec(string.format(sql_format.match_tp_list, "white", sql_escape(main), sql_escape("all"))) or {})[1] then
			table.insert(rows,
					  { "Remove the CDR whitelisting for this host from all domains",
					   " :rp wl! all " .. host, 
					   host = host, main = "all", cmd = "wl!",
					   fg = ifg, bg = ibg })
		else
			table.insert(rows,
					  { "Allow CDRs to this host from all domains",
					  " :rp wl ALL " .. host, 
					   host = host, main = "all", cmd = "wl",
					   fg = ifg, bg = ibg })
		end
		if (rpdb:exec(string.format(sql_format.match_tp_list, "black", sql_escape(main), sql_escape("all"))) or {})[1]then
			table.insert(rows,
					  { "Remove the CDR blacklisting for this host from all domains",
					   " :rp bl! all " .. host, 
					   host = host, main = "all", cmd = "bl!",
					   fg = ifg, bg = ibg })
		else
			table.insert(rows,
					  { "Blacklist CDRs to this host from all domains",
					  " :rp bl ALL " .. host, 
					   host = host, main = "all", cmd = "bl",
					   fg = ifg, bg = ibg })
		end
		if util.table.hasitem(exlist.third.white[main] or {}, host) then
			-- TODO remove temp wl
		else
			table.insert(rows,
					  { "Temporarily allow CDRs to this host from " .. main,
					   " :rp ex " .. main .. " " .. host, 
					   host = host, main = main, cmd = "ex",
					   fg = ifg, bg = ibg })
		end
		if util.table.hasitem(exlist.third.white["all"] or {}, host) then
			-- TODO remove temp wl
		else
			table.insert(rows,
					  { "Temporarily allow CDRs to this host from all domains",
					   " :rp ex ALL " .. host, 
					   host = host, main = main, cmd = "ex",
					   fg = ifg, bg = ibg })
		end
	end
        w.menu:build(rows)
        w:notify("Use j/k to move, Select action wish to take and press Enter or q to exit.", false)
    end,

    leave = function (w)
        w.menu:hide()
    end,
})

-- Adds keybindings for the policy menus
local key = lousy.bind.key
add_binds("policymenu", lousy.util.table.join({
    -- Select user agent
    key({}, "Return",
        function (w)
			local row = w.menu:get()
			if row then
				navto[w.view].selectedhost = row.host
    	        w:set_mode("policysubmenu")
			end
		end),

	-- TODO add in shortcut keys for commands
    -- Exit menu
    key({}, "q", function (w) w:set_mode() end),

}, menu_binds))

add_binds("policysubmenu", lousy.util.table.join({
	-- TODO make return just do the command, and Shift-Return put it in the input bar
	key({}, "Return",
        function (w)
			local row = w.menu:get()
            if row and row[2] then
                w:enter_cmd(util.string.strip(row[2]))
            end
        end),
	key({"Shift"}, "Return",
        function (w)
			local row = w.menu:get()
            if row and row[2] then
                w:enter_cmd(util.string.strip(row[2]))
            end
        end),
    -- Exit menu
    key({}, "q", function (w) w:set_mode() end),

}, menu_binds))

-- Add ex-mode commands
local cmd = lousy.bind.cmd
add_cmds({
    cmd({"requestpolicy", "rp"}, "view current page requests",
        function (w, a)
            if not a then
                w:set_mode("policymenu")
			else
				-- if called with an argument, try to interprate the command
				local args = util.string.split(util.string.strip(a or ""), " ")
				local aa = string.match(a, ".- (.*)")
				rp_command(args[1], w, aa)
			end
        end),
	cmd({"rp-whitelist", "rp-wl"}, "add a whitelist entry",
		function(w, a, o)
			rp_command((o.bang and "wl!") or "wl", w, a)
		end),
	cmd({"rp-blacklist", "rp-bl"}, "add a blacklist entry",
		function(w, a, o)
			rp_command((o.bang and "bl!") or "bl", w, a)
		end),
	cmd({"rp-exempt", "rp-ex"}, "grant temporary exceptions to request polices",
		function(w, a, o)
			rp_command((o.bang and "ex!") or "ex", w, a)
		end),
	cmd({"rp-set"}, "set request policy plugin behaviors",
		function(w, a)
			rp_command("set", w, a)
		end),	
	cmd({"rp-clear"}, "clear request policy exceptions",
		function(w, a)
			rp_command("clear", w, a)
		end),
})

-- Adds buffer command to invoke the policy menu and temp-allow all
-- ,pp = open policy menu
-- ,pa = allow all CDR from current host for this session
-- ,pt = toggle CDR filtering
local buf = lousy.bind.buf
add_binds("normal", {
	buf("^,pp$", function (w) w:set_mode("policymenu") end),
	buf("^,pa$", function(w) 
					if w.view and w.view.uri ~= "about:blank" then
						rp_command("ex", w, w.view.uri .. " all")
					end end),
	buf("^,pt$", function (w) rp_setting("requestpolicy", "toggle" ,w) end),
})

-- Status Bar Widget ==========================================================
--[[
-- Create the indictor widget on window creation
window.init_funcs.build_policy_indicator = function(w)
	local i = w.sbar.r
	i.policy = widget{type="label"}
	i.layout:pack(w.sbar.r.policy)
	i.layout:reorder(w.sbar.r.policy, 1)
	i.policy.fg = theme.buf_sbar_fg
	i.policy.font = theme.buf_sbar_font
	w:update_policy()
	-- Update indicator on tab change
	w.tabs:add_signal("switch-page", function (_,view)
		capi.luakit.idle_add(function() w:update_policy(w) return false end)
	end)
end

-- Update indicator on page navigation
webview.init_funcs.policy_update = function(view, w)
	view:add_signal("load-status", function (v, status)
		if status == "committed" or status == "failed" or status == "finished" then
			w:update_policy()
		end
	end)
end

-- Update contents of request policy widget
window.methods.update_policy = function(w)
	if not w.view then return end
    local pw = w.sbar.r.policy
	local text = "["
	if not filtering.acceptall then
		text = text .. "rp"
	else
		text = text .. "aa"
	end
	pw.text = text .. "]"
	pw:show()
end
]]
-- Call load()
load()
