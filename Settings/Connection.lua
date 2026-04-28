--[[
    Connection.lua
    Universal event/signal utility for Luau / Roblox.

    Event API:
      :Connect(fn, priority?, tag?)    -> ConnectionObject
      :Once(fn, priority?, tag?)       -> ConnectionObject
      :ConnectTagged(tag, fn, pri?)    -> ConnectionObject
      :GetConnectionsByTag(tag)        -> { ConnectionObject }
      :Wait(timeout?)                  -> ...args | nil, "timeout" | nil, "destroyed"
      :Fire(...)                       -> void
      :FireDeferred(...)               -> void
      :FireImmediate(...)              -> void
      :FireCollect(...)                -> { returns }
      :DisconnectAll()                 -> void
      :DisconnectByTag(tag)            -> void
      :Pause()                         -> void
      :Resume()                        -> void
      :Destroy()                       -> void
      :HasConnections()                -> boolean
      :ConnectionCount()               -> number
      :IsDestroyed()                   -> boolean
      :LinkToInstance(instance)        -> RBXScriptConnection

    Event fields:
      .MaxListeners                    -> number (0 = unlimited)
      .SafeMode                        -> boolean (pcall each callback)
      .OnConnectionChanged             -> fn(kind, connObj)?

    ConnectionObject API:
      .Connected                       -> boolean
      .Tag                             -> string?
      :Disconnect()                    -> void

    Notes:
      - Higher priority runs first.
      - Fire/FireDeferred use per-callback scheduling and clone callbacks for safe iteration.
      - FireImmediate/FireCollect are synchronous.
      - Waiters are resumed on Fire, timeout, or Destroy.
      - Fire variants on destroyed events are no-op.
      - SafeMode adds per-callback pcall overhead.
      - LinkToInstance uses Destroying when available, then falls back to AncestryChanged.
]]

local type = type
local assert = assert
local warn = warn
local pcall = pcall
local ipairs = ipairs
local setmetatable = setmetatable
local stringFormat = string.format

local tableRemove = table.remove
local tableInsert = table.insert
local tableClone = table.clone
local tableClear = table.clear
local tableUnpack = table.unpack

local taskSpawn = task.spawn
local taskDefer = task.defer
local taskDelay = task.delay

local coRunning = coroutine.running
local coYield = coroutine.yield
local coResume = coroutine.resume

-- Inserts a connection object by descending priority.
local function insertSorted(list, connObj)
    local priority = connObj._Priority
    for i, existing in ipairs(list) do
        if existing._Priority < priority then
            tableInsert(list, i, connObj)
            return
        end
    end
    tableInsert(list, connObj)
end

-- Executes a callback without allowing it to break the dispatch chain.
local function callSafe(fn, ...)
    local ok, err = pcall(fn, ...)
    if not ok then
        warn("[Connection] Callback error: " .. tostring(err))
    end
end

-- Notifies optional listeners about connection lifecycle changes.
local function notifyConnectionChanged(event, kind, connObj)
    local handler = event.OnConnectionChanged
    if type(handler) == "function" then
        taskDefer(handler, kind, connObj)
    end
end

-- Removes a pending waiter from the waiter list.
local function removeWaiter(waiters, waiter)
    for i = #waiters, 1, -1 do
        if waiters[i] == waiter then
            tableRemove(waiters, i)
            return true
        end
    end
    return false
end

-- Resumes a waiter only once, even if multiple paths race.
local function resumeWaiter(waiter, ...)
    if waiter.Resumed then
        return
    end
    waiter.Resumed = true
    local args = { ... }
    taskSpawn(function()
        local ok, err = coResume(waiter.Thread, tableUnpack(args))
        if not ok then
            warn("[Connection] Wait resume error: " .. tostring(err))
        end
    end)
end

local ConnectionObject = {}
ConnectionObject.__index = ConnectionObject

function ConnectionObject:Disconnect()
    if not self.Connected then
        return
    end

    local parent = self._Parent
    local removed = false
    if parent and not parent._Destroyed then
        local callbacks = parent._Callbacks
        for i = #callbacks, 1, -1 do
            if callbacks[i] == self then
                tableRemove(callbacks, i)
                removed = true
                break
            end
        end
        if removed then
            notifyConnectionChanged(parent, "disconnect", self)
        end
    end

    self.Connected = false
    self._Callback = nil
    self._Parent = nil
end

local Connection = {}
Connection.__index = Connection

function Connection.new()
    return setmetatable({
        _Callbacks = {},
        _Waiters = {},
        _Destroyed = false,
        _Paused = false,
        MaxListeners = 0,
        SafeMode = false,
        OnConnectionChanged = nil,
    }, Connection)
end

function Connection:Connect(callback, priority, tag)
    assert(not self._Destroyed, "Cannot Connect to a destroyed event")
    if type(callback) ~= "function" then
        error("Connection:Connect expected function, got " .. type(callback), 2)
    end

    local maxListeners = self.MaxListeners
    if maxListeners > 0 and #self._Callbacks >= maxListeners then
        warn(stringFormat(
            "[Connection] MaxListeners (%d) exceeded - possible leak (tag: %s)",
            maxListeners,
            tostring(tag)
        ))
    end

    local connObj = setmetatable({
        _Callback = callback,
        _Parent = self,
        _Priority = priority or 0,
        Connected = true,
        Tag = tag or nil,
    }, ConnectionObject)

    insertSorted(self._Callbacks, connObj)
    notifyConnectionChanged(self, "connect", connObj)
    return connObj
end

function Connection:Once(callback, priority, tag)
    assert(not self._Destroyed, "Cannot Once on a destroyed event")
    if type(callback) ~= "function" then
        error("Connection:Once expected function, got " .. type(callback), 2)
    end

    local conn
    conn = self:Connect(function(...)
        if conn and conn.Connected then
            conn:Disconnect()
        end
        callback(...)
    end, priority, tag)

    return conn
end

function Connection:ConnectTagged(tag, callback, priority)
    return self:Connect(callback, priority, tag)
end

function Connection:Wait(timeout)
    assert(not self._Destroyed, "Cannot Wait on a destroyed event")
    local thread = coRunning()
    assert(thread, "Connection:Wait must be called inside a coroutine or task")

    local waiter = {
        Thread = thread,
        Resumed = false,
    }

    tableInsert(self._Waiters, waiter)

    if type(timeout) == "number" and timeout >= 0 then
        taskDelay(timeout, function()
            if self._Destroyed then
                return
            end
            if removeWaiter(self._Waiters, waiter) then
                resumeWaiter(waiter, nil, "timeout")
            end
        end)
    end

    return coYield()
end

-- Resumes all pending waiters with the provided payload.
local function flushWaiters(self, ...)
    if #self._Waiters == 0 then
        return
    end

    local waiters = tableClone(self._Waiters)
    tableClear(self._Waiters)

    for _, waiter in ipairs(waiters) do
        resumeWaiter(waiter, ...)
    end
end

-- Shared dispatcher for Fire variants.
local function doFire(self, spawnFn, ...)
    if self._Destroyed or self._Paused then
        return
    end

    flushWaiters(self, ...)

    if #self._Callbacks == 0 then
        return
    end

    local safeMode = self.SafeMode
    local snapshot = tableClone(self._Callbacks)
    local args = { ... }

    for _, connObj in ipairs(snapshot) do
        if connObj.Connected and connObj._Callback then
            local fn = connObj._Callback
            if spawnFn then
                spawnFn(function()
                    if safeMode then
                        callSafe(fn, tableUnpack(args))
                    else
                        fn(tableUnpack(args))
                    end
                end)
            else
                if safeMode then
                    callSafe(fn, ...)
                else
                    fn(...)
                end
            end
        end
    end
end

function Connection:Fire(...)
    if self._Destroyed then
        return
    end
    doFire(self, taskSpawn, ...)
end

function Connection:FireDeferred(...)
    if self._Destroyed then
        return
    end
    doFire(self, taskDefer, ...)
end

function Connection:FireImmediate(...)
    if self._Destroyed then
        return
    end
    doFire(self, nil, ...)
end

function Connection:FireCollect(...)
    assert(not self._Destroyed, "Cannot FireCollect on a destroyed event")
    if self._Paused then
        return {}
    end

    flushWaiters(self, ...)

    local results = {}
    local safeMode = self.SafeMode
    local snapshot = tableClone(self._Callbacks)

    for _, connObj in ipairs(snapshot) do
        if connObj.Connected and connObj._Callback then
            local fn = connObj._Callback
            if safeMode then
                local ok, ret = pcall(fn, ...)
                if not ok then
                    warn("[Connection] FireCollect callback error: " .. tostring(ret))
                end
                tableInsert(results, ok and ret or nil)
            else
                tableInsert(results, fn(...))
            end
        end
    end

    return results
end

function Connection:DisconnectAll()
    if self._Destroyed then
        return
    end

    local hadConnections = #self._Callbacks > 0
    for i = #self._Callbacks, 1, -1 do
        local connObj = self._Callbacks[i]
        connObj.Connected = false
        connObj._Callback = nil
        connObj._Parent = nil
        self._Callbacks[i] = nil
    end

    if hadConnections then
        notifyConnectionChanged(self, "disconnect", nil)
    end
end

function Connection:DisconnectByTag(tag)
    assert(not self._Destroyed, "Cannot DisconnectByTag on a destroyed event")
    assert(type(tag) == "string", "DisconnectByTag: expected string tag")

    for i = #self._Callbacks, 1, -1 do
        local connObj = self._Callbacks[i]
        if connObj.Tag == tag then
            tableRemove(self._Callbacks, i)
            connObj.Connected = false
            connObj._Callback = nil
            connObj._Parent = nil
            notifyConnectionChanged(self, "disconnect", connObj)
        end
    end
end

function Connection:GetConnectionsByTag(tag)
    assert(not self._Destroyed, "Cannot GetConnectionsByTag on a destroyed event")
    assert(type(tag) == "string", "GetConnectionsByTag: expected string tag")

    local matches = {}
    for _, connObj in ipairs(self._Callbacks) do
        if connObj.Connected and connObj.Tag == tag then
            tableInsert(matches, connObj)
        end
    end

    return matches
end

function Connection:Pause()
    assert(not self._Destroyed, "Cannot Pause a destroyed event")
    self._Paused = true
end

function Connection:Resume()
    assert(not self._Destroyed, "Cannot Resume a destroyed event")
    self._Paused = false
end

function Connection:Destroy()
    if self._Destroyed then
        return
    end

    self:DisconnectAll()
    self._Destroyed = true
    self._Paused = true
    self.OnConnectionChanged = nil

    local waiters = tableClone(self._Waiters)
    tableClear(self._Waiters)
    for _, waiter in ipairs(waiters) do
        resumeWaiter(waiter, nil, "destroyed")
    end
end

function Connection:HasConnections()
    return (not self._Destroyed) and (#self._Callbacks > 0)
end

function Connection:ConnectionCount()
    if self._Destroyed then
        return 0
    end
    return #self._Callbacks
end

function Connection:IsDestroyed()
    return self._Destroyed
end

function Connection:LinkToInstance(instance)
    assert(typeof(instance) == "Instance", "LinkToInstance: expected Instance, got " .. typeof(instance))

    local linked
    local function destroyLinked()
        if linked then
            linked:Disconnect()
            linked = nil
        end
        self:Destroy()
    end

    local ok, destroyingSignal = pcall(function()
        return instance.Destroying
    end)

    if ok and destroyingSignal then
        linked = destroyingSignal:Connect(destroyLinked)
        return linked
    end

    linked = instance.AncestryChanged:Connect(function(_, parent)
        if parent == nil then
            destroyLinked()
        end
    end)
    return linked
end

function Connection.Create(names)
    assert(type(names) == "table", "Connection.Create: expected table of names")

    local events = {}
    for _, name in ipairs(names) do
        assert(type(name) == "string", "Connection.Create: all names must be strings")
        assert(not events[name], stringFormat("Connection.Create: duplicate event name %q", name))
        events[name] = Connection.new()
    end

    return events
end

return Connection
