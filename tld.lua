-- Module for checking public suffixes and tlds
local string = string
local table = table
local util = require("lousy.util")
local io = io
local tldlist = require("tldlist")

local print = print
local ipairs = ipairs
module("tld")

newgettld = function (host)
	if host and host ~= "" then
		local phost = host
		while phost do
			if tldlist.phost[phost] then
				return phost
			end
			p = string.match(phost, "(.-)%.")
			phost = string.match(phost, "%.(.*)")
			if phost and tldlist.phost["*." .. phost] then
				if tldlist.phost["!" .. p .. "." .. phost] then
					return phost
				else
					return p .. ".".. phost
				end
			end
		end
	end
end

newgetdomain = function (host)
	if not host or host == "" then
		return nil
	elseif string.match(host, "^[0-9%.]-$") then
		return host
	else
		local tl = newgettld(host)
		if tl == host then
			return nil
		elseif tl then
			local hb = util.table.reverse(util.string.split(host, "%."))
			local n = #(util.string.split(tl, "%.") or {}) + 1
			return hb[n] .. "." .. tl
		else
			return host
		end
	end
end

-- Returns the host's domain.effective.tld there is no regex way to do this
-- We check against a table of "public suffixes" from Mozilla
-- returns entire host string if given an IP (ipv4) or a
gettld = function (host)
	if host and host ~= "" then
		if string.match(host, "^[0-9%.]-$") then
			-- the host is an ipv4 address
			return host
		-- TODO add ipv6
		else
			local bits = util.table.reverse(util.string.split(host, "%.") or {})
			local p = bits[1]
			local n = 2
			while n <= #bits + 1 do
				if not bits[n] then
					-- Ran out of out bits before a public suffix was completed
					p = nil
					break
				elseif tldlist.phost["!" .. bits[n] .. "." .. p] then
					-- ! exception
					break
				elseif tldlist.phost["*." .. p] then
					-- wildcard match
					if bits[n + 1] then
						p = bits[n] .. "." .. p
					else
						-- Ran out of bits to complete a wild-card match
						p = nil
					end
					break
				elseif tldlist.phost[p] == nil then
					p = string.match(p, "%.(.*)")
					break
				end

				p = bits[n] .. "." .. p
				n = n + 1
			end
			return p
		end
	end
end


getdomain = function (host)
	if host and host ~= "" then
		if string.match(host, "^[0-9%.]-$") then
			-- the host is an ipv4 address
			return host
		-- TODO add ipv6
		else
			local bits = util.table.reverse(util.string.split(host, "%.") or {})
			local p = bits[1]
			local n = 2
			while n <= #bits + 1 do
				if not bits[n] then
					-- Ran out of out bits before a public suffix was completed
					p = nil
					break
				elseif tldlist.phost["!" .. bits[n] .. "." .. p] then
					-- ! exception
					p = bits[n] .. "." .. p
					break
				elseif tldlist.phost["*." .. p] then
					-- wildcard match
					if bits[n + 1] then
						p = bits[n + 1] .. "." .. bits[n] .. "." .. p
					else
						-- Ran out of bits to complete a wild-card match
						p = nil
					end
					break
				elseif tldlist.phost[p] == nil then
					break
				end

				p = bits[n] .. "." .. p
				n = n + 1
			end
			return p
		end
	end
end

test = {
	"10.8.4.1",
	"books.amazon.co.jp",
	"a.b.c.pvt.k12.ma.us",
	"search.google.com",
	"litter.kitty-cat.org",
	"a.b.c.kobe.jp",
	"a.b.city.kobe.jp",
	"kobe.jp",
	"c.kobe.jp",
	"momoko",
	"co.jp",
	"org",
	"pvt.k12.ma.us",
	"k12.ma.us",
	"",
}


for _,v in ipairs(test) do
	print(v .. " => " .. (getdomain(v) or "nil") .. " (" .. (gettld(v) or "-") .. ")")
	print(v .. " => " .. (newgetdomain(v) or "nil") .. " (" .. (newgettld(v) or "-") .. ")\n")
end
