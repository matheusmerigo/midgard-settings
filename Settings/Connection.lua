--[[
    Connection.lua
    Event utility for Luau / Roblox.

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
      .ConnectionChangedDeferred       -> boolean (default true)

    ConnectionObject API:
      .Connected                       -> boolean
      .Tag                             -> string?
      :Disconnect()                    -> void

    Notes:
      - Higher priority runs first.
      - Fire and FireDeferred schedule per callback; FireImmediate and FireCollect run synchronously.
      - Waiters resume on Fire, timeout, or Destroy.
      - LinkToInstance prefers Destroying, then falls back to AncestryChanged.
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
local tablePack = table.pack

local taskSpawn = task.spawn
local taskDefer = task.defer
local taskDelay = task.delay

local coRunning = coroutine.running
local coYield = coroutine.yield
local coResume = coroutine.resume

local function packArgs(...)
    if type(tablePack) == "function" then
        return tablePack(...)
    end
    return { n = select("#", ...), ... }
end

local function unpackArgs(args)
    return tableUnpack(args, 1, args.n or #args)
end

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

local function removeCallback(list, connObj)
    for i = #list, 1, -1 do
        if list[i] == connObj then
            tableRemove(list, i)
            return true
        end
    end
    return false
end

local function callSafe(fn, ...)
    local args = packArgs(...)
    local ok, err = xpcall(function()
        return fn(unpackArgs(args))
    end, debug.traceback)
    if not ok then
        warn("[Connection] Callback error: " .. tostring(err))
    end
end

local function dispatchCallback(safeMode, fn, spawnFn, packedArgs, ...)
    if spawnFn then
        spawnFn(function()
            if safeMode then
                callSafe(fn, unpackArgs(packedArgs))
            else
                fn(unpackArgs(packedArgs))
            end
        end)
        return
    end

    if safeMode then
        callSafe(fn, ...)
    else
        fn(...)
    end
end

local function collectCallback(safeMode, fn, ...)
    if not safeMode then
        return fn(...)
    end

    local ok, ret = pcall(fn, ...)
    if not ok then
        warn("[Connection] FireCollect callback error: " .. tostring(ret))
    end
    return ok and ret or nil
end

local function notifyConnectionChanged(event, kind, connObj)
    local handler = event.OnConnectionChanged
    if type(handler) ~= "function" then
        return
    end

    if event.ConnectionChangedDeferred == false then
        callSafe(handler, kind, connObj)
    else
        taskDefer(function()
            callSafe(handler, kind, connObj)
        end)
    end
end

local function addTaggedConnection(event, connObj)
    local tag = connObj.Tag
    if type(tag) ~= "string" then
        return
    end

    local tagIndex = event._TagIndex
    local bucket = tagIndex[tag]
    if not bucket then
        bucket = {}
        tagIndex[tag] = bucket
    end
    bucket[#bucket + 1] = connObj
end

local function removeTaggedConnection(event, connObj)
    local tag = connObj.Tag
    if type(tag) ~= "string" then
        return
    end

    local tagIndex = event._TagIndex
    local bucket = tagIndex[tag]
    if not bucket then
        return
    end

    for i = #bucket, 1, -1 do
        if bucket[i] == connObj then
            tableRemove(bucket, i)
            break
        end
    end

    if #bucket == 0 then
        tagIndex[tag] = nil
    end
end

local function clearConnection(connObj)
    connObj.Connected = false
    connObj._Callback = nil
    connObj._Parent = nil
end

local function removeWaiter(waiters, waiter)
    for i = #waiters, 1, -1 do
        if waiters[i] == waiter then
            tableRemove(waiters, i)
            return true
        end
    end
    return false
end

local function resumeWaiter(waiter, ...)
    if waiter.Resumed then
        return
    end
    waiter.Resumed = true
    if waiter.TimeoutHandle then
        task.cancel(waiter.TimeoutHandle)
        waiter.TimeoutHandle = nil
    end
    local args = packArgs(...)
    taskSpawn(function()
        local ok, err = coResume(waiter.Thread, unpackArgs(args))
        if not ok then
            warn("[Connection] Wait resume error: " .. tostring(err))
        end
    end)
end

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

-- Connection objects
local ConnectionObject = {}
ConnectionObject.__index = ConnectionObject

function ConnectionObject:Disconnect()
    if not self.Connected then
        return
    end

    local parent = self._Parent
    local removed = false
    if parent and not parent._Destroyed then
        removed = removeCallback(parent._Callbacks, self)
        if removed then
            removeTaggedConnection(parent, self)
            notifyConnectionChanged(parent, "disconnect", self)
        end
    end

    clearConnection(self)
end

local Connection = {}
Connection.__index = Connection

function Connection.new()
    return setmetatable({
        _Callbacks = {},
        _Waiters = {},
        _TagIndex = {},
        _Links = {},
        _Destroyed = false,
        _Paused = false,
        MaxListeners = 0,
        SafeMode = false,
        OnConnectionChanged = nil,
        ConnectionChangedDeferred = true,
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
    addTaggedConnection(self, connObj)
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
        waiter.TimeoutHandle = taskDelay(timeout, function()
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

local function doFire(self, spawnFn, ...)
    if self._Destroyed or self._Paused then
        return
    end

    flushWaiters(self, ...)

    if #self._Callbacks == 0 then
        return
    end

    local safeMode = self.SafeMode
    local args = packArgs(...)
    local callbacks = self._Callbacks

    if #callbacks == 1 then
        local connObj = callbacks[1]
        if connObj and connObj.Connected and connObj._Callback then
            dispatchCallback(safeMode, connObj._Callback, spawnFn, args, ...)
        end
        return
    end

    local snapshot = tableClone(callbacks)

    for _, connObj in ipairs(snapshot) do
        if connObj.Connected and connObj._Callback then
            dispatchCallback(safeMode, connObj._Callback, spawnFn, args, ...)
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
    local callbacks = self._Callbacks

    if #callbacks == 1 then
        local connObj = callbacks[1]
        if connObj and connObj.Connected and connObj._Callback then
            results[1] = collectCallback(safeMode, connObj._Callback, ...)
        end
        return results
    end

    local snapshot = tableClone(callbacks)

    for _, connObj in ipairs(snapshot) do
        if connObj.Connected and connObj._Callback then
            tableInsert(results, collectCallback(safeMode, connObj._Callback, ...))
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
        clearConnection(connObj)
        self._Callbacks[i] = nil
    end
    tableClear(self._TagIndex)

    if hadConnections then
        notifyConnectionChanged(self, "disconnect", nil)
    end
end

function Connection:DisconnectByTag(tag)
    assert(not self._Destroyed, "Cannot DisconnectByTag on a destroyed event")
    assert(type(tag) == "string", "DisconnectByTag: expected string tag")

    local bucket = self._TagIndex[tag]
    if not bucket then
        return
    end

    local taggedSnapshot = tableClone(bucket)
    for _, connObj in ipairs(taggedSnapshot) do
        removeCallback(self._Callbacks, connObj)
        if connObj.Connected then
            clearConnection(connObj)
            notifyConnectionChanged(self, "disconnect", connObj)
        end
    end

    self._TagIndex[tag] = nil
end

function Connection:GetConnectionsByTag(tag)
    assert(not self._Destroyed, "Cannot GetConnectionsByTag on a destroyed event")
    assert(type(tag) == "string", "GetConnectionsByTag: expected string tag")

    local matches = {}
    local bucket = self._TagIndex[tag]
    if not bucket then
        return matches
    end

    for _, connObj in ipairs(bucket) do
        if connObj.Connected then
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
    self.ConnectionChangedDeferred = nil

    for i = #self._Links, 1, -1 do
        local linked = self._Links[i]
        self._Links[i] = nil
        if linked and linked.Connected then
            linked:Disconnect()
        end
    end

    local waiters = tableClone(self._Waiters)
    tableClear(self._Waiters)
    tableClear(self._TagIndex)
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
    local destroyed = false
    local function destroyLinked()
        if destroyed then
            return
        end
        destroyed = true
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
        tableInsert(self._Links, linked)
        return linked
    end

    linked = instance.AncestryChanged:Connect(function(_, parent)
        if parent == nil then
            destroyLinked()
        end
    end)
    tableInsert(self._Links, linked)
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
