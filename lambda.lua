-- untyped lambda calculus in lua
-- vim: set tw=76 ts=4 et fdm=marker fmr=<<<,>>> :

-- data & types <<<

env = {}

-- PRIM id  -- variables

env.nat = {
    O   = { },
    S   = { "nat" },
}

env.term = {
    app = { "term", "term" },
    lam = { "term" },
    var = { "nat" },
    ref = { "id" },
}

-- >>>

-- values <<<

env.v0 = { "O" }
env.v1 = { "S", env.v0 }
env.v2 = { "S", env.v1 }

env.K = {
"lam",
    { "lam",
        { "var",
            1,
        },
    },
}

env.S = {
"lam",
    { "lam",
        { "lam",
            { "app",
                { "app",
                    { "var",
                        2,
                    },
                    { "var",
                        0,
                    },
                },
                { "app",
                    { "var",
                        1,
                    },
                    { "var",
                        0,
                    },
                },
            }
        },
    },
}

env.I = {
"app",
    { "app",
        { "ref", "S" },
        { "ref", "K" },
    },
    { "ref", "K" },
}

env.inc = {
"lam",
    { "app",
        { "S" },
        { "var", 0 },
    }
}

env.plus = {
"lam",
    { "lam",
        { "lam",
            { "rec", { "var", 1 },
                O = { "var", 0 },
                S = { "lam",
                        { "S",
                            { "app",
                                { "app",
                                    { "app", { "var", 3 }, { "var", 3 } },
                                    { "var", 0 }
                                },
                                { "var", 1 }
                            },
                        },
                    }
            }
        }
    }
}

fun_plus = { "app", _fun_plus, _fun_plus }

-- >>>

-- lua helpers <<<

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
    local cname = tm[1]
    if cname == "app" then
        return isClosedTerm(tm[2],maxidx) and isClosedTerm(tm[3],maxidx)
    elseif cname == "var" then
        return tm[2] < maxidx
    elseif cname == "lam" then
        return isClosedTerm(tm[2], maxidx+1)
    else
        return true
    end
end

function raiseVarAbove(tm,raiseidx)
    raiseidx = raiseidx or -1
    local cname = tm[1]
    if cname == "var" then
        if tm[2] > raiseidx then
            return { "var", tm[2]+1 }
        end
    elseif cname == "lam" then
        local ret = raiseVarAbove(tm[2], raiseidx+1)
        if ret then
            return { "lam", ret }
        end
    else
        return walk_all(raiseVarAbove, tm, raiseidx)
    end
end

-- >>>

-- reduction <<<

-- substitute t2 into t1 at variable index i
function subst(t1,t2,i)
    local cname = t1[1]
    if cname == "lam" then
        local ret = subst(t1[2], t2, i+1)
        if ret then
            return { "lam", ret }
        end
    elseif cname == "var" then
        if t1[2] == i then
            return raiseVarAbove(t2,-1) or t2
        elseif t1[2] > i then
            return { "var", t1[2]-1 }
        else
            return nil, "not substituted"
        end
    else
        -- generic traversal
        local ret = walk_all(subst, t1, t2, i)
        if ret then
            return ret
        end
    end
    return nil, "no substitution"
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

function beta(tm, lazy)
    local cname = tm[1]
    if cname == "app" then
        local red = beta(tm[2],lazy)
        if red and lazy then
            return { "app", red, tm[3] }
        else
            -- app may be reducible if first term is lambda or partially applied constructor
            local red = tryApply(tm[2], tm[3])
            if red then
                return red
            end
            -- else try generic tree walk
        end
    end
    -- generic tree walk
    local red = walk_step(beta,tm,lazy)
    if red then
        return red
    else
        return nil, "Y U NO red in |- * ?"
    end
end

-- pattern matching
function iota(tm)
    local cname = tm[1]
    if cname == "rec" then
        local v = tm[2]
        local cname = v[1]
        local _ty, c = findConstructorType(cname)
        if _ty and _ty ~= "var" and _ty ~= "app" then
            assert(_ty ~= "lam")
            local f = tm[cname]
            if f then
                for k = 1, #c do
                    f = { "app", f, v[k+1] }
                end
                return f
            end
        end
    end
    -- generic walk
    local red = walk_step(iota,tm)
    if red then
        return red
    else
        return nil, "MATCHED _ALL_ THE PATTERNS!"
    end
end

function delta(tm)
    local cname = tm[1]
    if cname == "ref" then
        local v = env[tm[2]]
        if not v then
            return nil, "undefined variable '"..tostring(tm[2]).."'"
        else
            return v
        end
    end
    -- generic walk
    local red = walk_step(delta,tm)
    if red then
        return red
    else
        return nil, "SUBSTITUTED _ALL_ THE VARIABLES!"
    end
end

function reduce(tm, max)
    max = max or 100
    local red
    if max < 1 then
        return nil, "timeout"
    else
        for _,f in ipairs{ iota, beta, delta } do
            local red = f(tm)
            if red then
                return reduce(red, max-1)
            end
        end
        return tm
    end
end

-- >>>

-- pretty printing <<<

-- tostring
function dump(tm)
    if type(tm) == "table" then
        local cname = tm[1]
        if cname == "lam" then
            return "($"..dump(tm[2])..")"
        elseif cname == "var" then
            return "{"..tostring(tm[2]).."}"
        elseif cname == "app" then
            return "("..dump(tm[2])..dump(tm[3])..")"
        else
            return "<?>"
        end
    else
        return "<?>"
    end
end

function show(tm)
    _show(tm,"\n")
    io.write "\n"
end

function _show(tm, indent)
    if type(tm) == "table" then
        local cname = tm[1]
        if cname == "lam" then
            io.write("$")
            _show(tm[2], indent.." ")
        elseif cname == "var" then
            io.write("{",tostring(tm[2]),"}")
        elseif cname == "ref" then
            io.write("@[",tostring(tm[2]),"]")
        elseif cname == "app" then
            io.write "+"
            _show(tm[2], indent.."|")
            io.write(indent.."\\")
            _show(tm[3], indent.." ")
        elseif cname == "rec" then
            io.write "?"
            _show(tm[2], indent..".")
            for k,v in pairs(tm) do
                if type(k) ~= "number" then
                    local s = "#"..k..":"
                    io.write(indent,s)
                    _show(v,indent..string.rep(" ",#s))
                end
            end
        else
            local _ty, c = findConstructorType(cname)
            if not _ty then
                io.write "<?>"
            else
                io.write(cname,"*")
                indent = indent .. string.rep(" ", #cname)
                local nfields = #c
                for k = 1, nfields do
                    local endc = k ~= nfields and "!" or " "
                    if k ~= 1 then
                        io.write(indent, endc)
                    end
                    local v = tm[k+1]
                    if type(v) == "table" then
                        _show(v, indent..endc)
                    elseif v == nil then
                        io.write "_"
                    else
                        io.write("<",tostring(v),">")
                    end
                end
            end
        end
    else
        return nil
    end
end

-- >>>

