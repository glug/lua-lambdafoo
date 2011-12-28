-- interface/instance based FP example / draft
-- vim: set tw=76 ts=4 et fdm=marker fmr=<<<,>>> :

-- types <<<

dtype = {}

dtype.nat = {}
dtype.nat.O = {}
dtype.nat.S = { "nat" }

dtype.natList = {}
dtype.natList.Nil = {}
dtype.natList.Cons = { "nat", "natList" }

dtype.void = {}

dtype.unit = {}
dtype.unit.tt = {}

-- >>>

-- valid typed values <<<

val_0 = { "O" , _type = "nat" }
val_1 = { "S", val_0, _type = "nat" }
val_2 = { "S", val_1, _type = "nat" }

val_nil = {
    "Nil",
    _type = "natList"
}

val_list = {
    "Cons",
    val_2,
    {
        "Cons",
        val_0,
        {
            "Cons",
            val_1,
            val_nil,
            _type = "natList"
        },
        _type = "natList"
    },
    _type = "natList"
}

-- >>>

-- valid untyped values <<<

uval_0 = { "O" }
uval_1 = { "S", uval_0 }
uval_2 = { "S", uval_1 }

uval_list = { "Cons", val_2,
                { "Cons", val_0,
                    { "Cons", val_1,
                        { "Nil" }}}}

-- >>>

-- invalid values <<<
inval_1 = { "S", val_nil, _type = "nat" }
inval_2 = { "S", inval_1, _type = "nat" }

inval_list = {
    "Cons",
    val_2,
    {
        "Cons",
        val_0,
        {
            "Cons",
            val_1,
            {
                "Nil",
                {
                    "Nil",
                    _type = "natList"
                },
                _type = "natList"
            },
            _type = "natList"
        },
        _type = "natList"
    },
    _type = "natList"
}

-- >>>

-- field checker <<<
local function checkFieldsWith(f_rec, constructor, val, _type, _indent)
    -- wrong number of fields
    local df = (#val-1) - #constructor
    if df ~= 0 then
        local asdf = math.abs(df)
        return nil, string.format(
                        "\n%svalue for constructor %s of type %s "..(
                            (df < 0)
                                and "is missing %d field%s"
                                or  "contains %d superfluous value%s"
                            ),
                        string.rep(" ",_indent*2),
                        val[1],
                        _type,
                        asdf,
                        (asdf == 1) and "" or "s")
    end
    -- check fields
    for i, v in ipairs(val) do
        -- skip constructor
        if i ~= 1 then
            local fieldtype = constructor[i-1]
            print(string.format("%s #%d : %s?",
                                    string.rep(" ", _indent*4),
                                    i-1,
                                    fieldtype))
            local t, _err = f_rec(v,fieldtype, _indent+1)
            if not t then
                return nil, string.format(
                                "\n%sinvalid constructor field #%d for value of type %s: %s",
                                string.rep(" ",_indent*2), i-1, _type, _err)
            end
        end
    end
    return _type
end
-- >>>

-- type checker / inference <<<
function checkType(val, _type, _indent)
    _indent = _indent or 0
    -- have value?
    if not val then
        return nil, string.format("%sY U NO VALUE???", string.rep(" ", _indent*2))
    end
    local constructor
    -- need to find type?
    _type = _type or val._type
    if not _type then
        for ty, constructors in pairs(dtype) do
            -- check if constructor exists
            local foo = constructors[val[1]]
            if foo then
                print(string.format("%s%s { ... } : %s?",
                                        string.rep(" ",_indent*4), val[1], ty))
                _type = ty
                constructor = foo
                break
            end
        end
    else
--        print(string.format("%s%s : %s!?", string.rep(" ", _indent*4), val[1], _type))
        -- check if constructor for this type exists
        constructor = dtype[_type][val[1]]
        if not constructor then
            return nil, string.format("\n%sinvalid constructor %s for type %s",
                                string.rep(" ",_indent*2), val[1], _type)
        end
    end
    -- no type match
    if not _type then
        return nil, string.format("\n%sunknown constructor %s",
                                    string.rep(" ", _indent*2),
                                    val[1])
    end
    -- check type, infer lower levels
    return checkFieldsWith(checkType, constructor, val, _type, _indent)
end
-- >>>

