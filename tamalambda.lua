-- untyped lambda calculus in lua, using tamale for table matching
-- vim: set tw=76 ts=4 et fdm=marker fmr=<<<,>>> :

pcall(require, "luarocks.loader")

require "tamale"

-- tamale prep <<<

function match(tm)
    return function(...)
        return tamale.matcher(...)(tm)
    end
end

default = tamale.var"_"

_matchvar = function(id)
    local vname = "_"..id
    if not _G[vname] then
        _G[vname] = tamale.var(id)
    end
    return _G[vname]
end

_matchvar "tm1"
_matchvar "tm2"
_matchvar "var"
_matchvar "val"

-- >>>

-- data & types <<<

env = {}

-- PRIM_id  -- variables
-- PRIM_num -- lambda / de brujin indices

-- special behavior for:
--   + match
--   + Record
--     * Type
--     * Class
--     ...

--[===[

SomeType = ld [[

]]

Inductive list (A : Type) : Type :=
    nil : list A | cons : A -> list A -> list A

data list a where
    nil : list a
    cons : a -> list a

--]===]

env.nat = {
    O   = { },
    S   = { "nat" },
}

env.term = {
    app = { "term", "term" },
    lam = { "term" },
    var = { "PRIM_num" },
    ref = { "PRIM_id" },
}

env.natList = {
    natNil = { },
    natCons = { "nat", "natList" }
}

-- >>>

-- lua helpers <<<

-- pack a result into a table with constructor field added, else return nil
function pack(v)
    return function(x,...)
        if x then
            return {v, x, ...}
        end
    end
end

function copy(t)
    local newt = {}
    for k,v in pairs(t) do
        newt[k] = v
    end
    return newt
end

-- walk over table fields, apply f on table fields until non-nil/false return value
--  if f returns false, try next field
--  if f returns a true value, break and return modified structure
function walk_step(f, t, ...)
    for i,v in pairs(t) do
        if type(v) == "table" then
            local ret = f(v, ...)
            if ret then
                -- copy, modify & return
                local t2 = copy(t)
                t2[i] = ret
                return t2
            end
        end
    end
end

-- same as above, but modify all table fields
function walk_all(f,t, ...)
    -- generic traversal
    local t2
    for i, v in pairs(t) do
        if type(v) == "table" then
            local ret = f(v, ...)
            -- modify result if substitution successful
            if ret then
                t2 = t2 or copy(t)
                t2[i] = ret
            end
        end
    end
    return t2
end

-- >>>

-- handling of non-standard constructors <<<

function findConstructorType(cname)
    for tname, constructors in pairs(env) do
        local c = constructors[cname]
        if c then
            return tname, c
        end
    end
    return nil, "undefined constructor "..cname
end

-- >>>

-- closed and open terms <<<

function isClosedTerm(tm, maxidx)
    maxidx = maxidx or 0
    return match(tm) {
        { { "app", _tm1, _tm2 }, function(c) return isClosedTerm(c.tm1,maxidx)
                                                and isClosedTerm(c.tm2,maxidx) end },
        { { "var", _var }, function(c) return c.var < maxidx end },
        { { "lam", _tm1 }, function(c) return isClosedTerm(c.tm1, maxidx+1) end },
        { default, true }
    }
end

function raiseVarAbove(tm,raiseidx)
    raiseidx = raiseidx or -1
    return match(tm) {
        { { "var", _var }, function(c) if c.var > raiseidx then return { "var", c.var+1 } end end },
        { { "lam", _tm1 }, function(c) return pack"lam"(raiseVarAbove(c.tm1, raiseidx+1)) end },
        { default, function() return walk_all(raiseVarAbove, tm, raiseidx) end }
    }
end

-- >>>

-- reduction <<<

-- substitute t2 into t1 at variable index i
function subst(t1,t2,i)
    return match(t1) {
        { { "lam", _tm1 }, function(c) return pack"lam"(subst(c.tm1, t2, i+1)) end },
        { { "var", _var }, function(c)
                                if c.var == i then
                                    return raiseVarAbove(t2,-1) or t2
                                elseif c.var > i then
                                    return { "var", c.var - 1 }
                                end
                            end },
        { default, function() return walk_all(subst,t1,t2,i) end }
    }
end

-- try applying t2 to t1
-- works if t1 is a 'lam' or a partially applied constructor
function tryApply(t1,t2)
    local cname = t1[1]
    if cname == "lam" then
        return subst(t1[2],t2,0) or t1[2]
    else
        local _ty, c = findConstructorType(cname)
        -- valid and partially applied constructor?
        if _ty and #t1 < #c + 1 then
            local t = copy(t1)
            table.insert(t,t2)
            return t
        end
    end
end

function beta(tm, _ign, lazy)
    local function walk() return walk_step(beta, tm, _ign, lazy) end
    return match(tm) {
        { { "app", _tm1, _tm2 }, function(c)
                                    return lazy and pack"app"(beta(c.tm1,_ign,lazy), c.tm2)
                                        or tryApply(c.tm1, c.tm2)
                                        or walk()
                                 end },
        { default, walk }
    }
end


-- helper: decrement and turn zero into false
local function dec(n)
    if type(n) == "number" then
        n = n - 1
        return n > 0 and n
    end
end

-- pattern matching
function iota(tm,many)
    local function walk()
        local red = (many and walk_all or walk_step)(iota,tm)
        return red and iota(red,dec(many)) or red
    end
    -- match
    return match(tm) {
        { { "rec", _val }, function(c)
                                local cname = c.val[1]
                                local _ty, cfields = findConstructorType(cname)
                                if cname ~= "term" and _ty then
                                    local f = tm[cname]
                                    if f then
                                        for k = 1, #cfields do
                                            f = pack"app"(f, c.val[k+1])
                                        end
                                        return f
                                    end
                                end
                            end, partial = true },
        { default, walk }
    }
end

function delta(tm,many)
    local function walk()
        local red = (many and walk_all or walk_step)(delta,tm,many)
        return red and delta(red,dec(many)) or red
    end
    return match(tm) {
        { { "ref", _var }, function(c) return env[c.var] end },
        { default, walk }
    }
end

function reduce(tm, max)
    max = max or 100
    if max < 1 then
        return nil, "timeout"
    else
        for _,f in ipairs{ delta, iota, beta } do
            local red = f(tm,true)
            if red then
                return reduce(red, max-1)
            end
        end
        return tm
    end
end

-- >>>

-- ugly printing <<<

-- tostring
function dump(tm)
    if type(tm) == "table" then
        return match(tm) {
            { { "lam", _tm1 },      function(c) return "($"..dump(c.tm1)..")" end },
            { { "var", _var },      function(c) return "{"..tostring(c.var).."}" end },
            { { "app", _tm1, _tm2 },function(c) return "("..dump(c.tm1)..dump(c.tm2)..")" end },
            { { "ref", _var },      function(c) return '@"'..tostring(c.var)..'"' end },
            { { "rec", _val },      function(c)
                                        local str = "?"..dump(c.val).."{|"
                                        for k,v in pairs(tm) do
                                            if type(k) ~= "number" then
                                                str = str..tostring(k)..":"..dump(v).."|"
                                            end
                                        end
                                        str = str.."}"
                                        return str
                                    end,
                                    partial = true },
            { default, function()
                            local cname = tm[1]
                            local _ty, cfields = findConstructorType(cname)
                            if not _ty then return "<?>" end
                            local str = cname
                            local nfields = #cfields
                            if nfields > 0 then
                                str = str.."["..dump(tm[2])
                                for k=2,nfields do
                                    str = str..","..dump(tm[k+1])
                                end
                                str = str.."]"
                            end
                            return str
                        end }
        }
    elseif tm == nil then
        return "_"
    else
        return "<?>"
    end
end

function show(tm)
    _show(tm,"\n")
    io.write "\n"
end

function _show(tm, indent)
    local _cond = type(tm)
    if _cond == "table" then
        match(tm) {
            { { "lam", _tm1 },      function(c) io.write"$" ; _show(c.tm1, indent.." ") end },
            { { "var", _var },      function(c) io.write("{",tostring(c.var),"}") end },
            { { "ref", _var },      function(c) io.write('@"',tostring(c.var),'"') end },
            { { "app", _tm1, _tm2 },function(c)
                                        io.write "+" ; _show(c.tm1, indent.."|")
                                        io.write(indent,"\\") ; _show(c.tm2, indent.." ")
                                    end },
            { { "rec", _val },      function(c)
                                        io.write "?" ; _show(c.val, indent..".")
                                        for k,v in pairs(tm) do
                                            if type(k) ~= "number" then
                                                local s = "#"..tostring(k)..":"
                                                io.write(indent,s)
                                                _show(v,indent..string.rep(" ",#s))
                                            end
                                        end
                                    end,
                                    partial = true },
            { default,  function()
                            local cname = tm[1]
                            local _ty, cfields = findConstructorType(cname)
                            if not _ty then return io.write "<?>" end
                            io.write(cname)
                            indent = indent..string.rep(" ", #cname)
                            local nfields = #cfields
                            if nfields > 0 then
                                io.write "["
                                _show(tm[2], indent..(nfields ~= 1 and "!" or " "))
                                for k = 2, nfields do
                                    local indent = indent..(k ~= nfields and "!" or " ")
                                    io.write(indent)
                                    _show(tm[k+1], indent)
                                end
                                io.write "]"
                            end
                        end }
        }
    elseif _cond == "nil" then
        io.write "_"
    else
        io.write("<",tostring(tm),">")
    end
end

-- >>>

-- whacky parsing <<<

--  special:
--      ( )
--      numbers
--      whitespace

function tokenize(str)
    -- character classes
    local pat_endtok = "[() \t\r\n\v]"
    local pat_paren = "[()]"
    -- state
    local accumulator
    -- result
    local tokens = { "(" }
    -- computation
    for c in string.gmatch(str,".") do
        -- id
        if accumulator then
            -- end & start next or append
            if string.find(c, pat_endtok) then
                table.insert(tokens,table.concat(accumulator))
                if string.find(c, pat_paren) then
                    table.insert(tokens, c)
                end
                accumulator = nil
            else
                table.insert(accumulator, c)
            end
        else
            if string.find(c,pat_paren) then
                table.insert(tokens, c)
            elseif string.find(c, pat_endtok) then
                -- ignore ws
            else
                accumulator = { c }
            end
        end
    end
    if accumulator then
        table.insert(tokens, table.concat(accumulator))
    end
    tokens[#tokens+1] = ")"
    return tokens
end

--[[ grammar (sort of)

expr  ::= '(' exprlist ')'
        | atom

exprlist  ::= expr^*

atom  ::= id
        | number

number ::= digit valchars^*

id ::= id1char valchars^*

valchars ::= << all but parens "()" and whitespace " \t\r\n\v" >>
digit ::= << 0-9 >>
id1char ::=  << any non-digit valchars >>

--]]

function parseAt(toks,i)
    i = i or 1
    local ret = {}
    local tok = toks[i]
    if tok == ")" then
        error "unbalanced parentheses"
    elseif tok == "(" then
        i = i + 1
        while toks[i] ~= ")" do
            local val, newi = parseAt(toks,i)
            if not val then
                error "invalid state"
            else
                table.insert(ret, val)
                i = newi
            end
        end
        return ret, i+1
    else
        if string.find(string.sub(tok,1,1),"%d") then
            return tonumber(tok), i+1   -- NOTE extend to other formats later
        else
            return tok, i+1
        end
    end
end

-- rewrite all 'rec' subentries
--   from (case <constructor> <value>)
--   to   <constructor> = { <value> }
function fixCase(tm)
    local cname = tm[1]
    if cname == "rec" then
        for k,v in ipairs(tm) do
            if v[1] == "case" then
                tm[v[2]] = v[3]
                tm[k] = nil
            end
        end
    end
    -- generic walk
    local red = walk_all(fixCase,tm)
    if red then
        return red
    else
        return nil, "MATCHED _ALL_ THE PATTERNS!"
    end
end

function loadlam(str)
    local tm = parseAt(tokenize(str))[1]
    return fixCase(tm) or tm
end

-- >>>

-- some values <<<

function ld(s,nored)
    local v, _err = loadlam(s)
    if v and not nored then
        local v = delta(v,true) or v
        return reduce(v) or v, _err
    else
        return v, _err
    end
end

env.v0 = ld [[ (O) ]]
env.v1 = ld [[ (S (ref v0)) ]]
env.v2 = ld [[ (S (ref v1)) ]]

env.K = ld [[
(lam
  (lam
    (var 1)))
]]

env.S = ld [[
(lam
  (lam
    (lam
      (app
        (app (var 2) (var 0))
        (app (var 1) (var 0))))))
]]

env.I = ld [[
(app
  (app (ref S) (ref K))
  (ref K))
]]

env.inc = ld [[
(lam
  (app (S) (var 0)))
]]

env._plus = ld [[
(lam
  (lam
    (lam
      (rec (var 1)
        (case O (var 0))
        (case S (lam
                    (S
                      (app (app (app (var 3) (var 3)) (var 0))
                           (var 1)))))))))
]]

env.plus = ld [[ (app (ref _plus) (ref _plus)) ]]

env.twoplustwo = ld [[ (app (app (ref plus) (ref v2)) (ref v2)) ]]

env.someNatList = ld [[
(natCons (ref v2)
         (natCons (ref v1)
                  (natCons (ref v0)
                           (natNil))))
]]

-- >>>

