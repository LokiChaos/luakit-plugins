-------------------------------------------------------------------------------
--                                                                           --
-- No-Scipt Status Widget                                                    --
-- Adds a simple, skinnable, widget to the status bar to indicate the        --
-- current status of scripts and plugins                                     --
--                                                                           --
-------------------------------------------------------------------------------

local string = string
local window = window
local webview = webview
local widget = widget
local theme = theme
local luakit = luakit
local domain_props = domain_props
local lousy = require("lousy")
local history = require("history")

module("plugins.nscript_widget")

-- Strings widget uses
local script_str = { enabled = "s", disabled = "!s" }
local plugin_str = { enabled = "p", disabled = "!p" }


-- Load themes, if undefined fallback
theme.nsw_enabled  = theme.nsw_enabled or "#0f0"
theme.nsw_disabled = theme.nsw_disabled or "#f00"

-- Create the indictor widget on window creation
window.init_funcs.build_ns_indicator = function(w)
	local i = w.sbar.r
	i.noscr = widget{type="label"}
	i.layout:pack(w.sbar.r.noscr)
	i.layout:reorder(w.sbar.r.noscr, 2)	
	i.noscr.font = theme.buf_sbar_font
	w:update_noscr()
	-- Update indicator on tab change
	w.tabs:add_signal("switch-page", function (_,view)
		luakit.idle_add(function() w:update_noscr(w) return false end)
	end)
end

-- Update indicator on page navigation
webview.init_funcs.noscr_update = function(view, w)
	view:add_signal("load-status", function (v, status)
		if status == "committed" or status == "failed" or status == "finished" then
			w:update_noscr()
		end
	end)
end

-- Method wrapper
window.methods.update_noscr = function(w)
	if not w.view then return end
    local scripts = w.view.enable_scripts
    local plugins = w.view.enable_plugins
    local noscr = w.sbar.r.noscr
    local tmpl = '<span foreground="%s">%s</span> <span foreground="%s">%s</span>'
    noscr.text = string.format(tmpl, 
    ( scripts and theme.nsw_enabled ) or theme.nsw_disabled,
    ( scripts and script_str.enabled ) or script_str.disabled,
    ( plugins and theme.nsw_enabled ) or theme.nsw_disabled,
    ( plugins and plugin_str.enabled ) or plugin_str.disabled)
	noscr:show()
end
