# Sugar

[![Build Status](https://travis-ci.org/SimonDanisch/Sugar.jl.svg?branch=master)](https://travis-ci.org/SimonDanisch/Sugar.jl)

[![Build status](https://ci.appveyor.com/api/projects/status/n3eaobx5e3an2k40/branch/master?svg=true)](https://ci.appveyor.com/project/SimonDanisch/sugar-jl/branch/master)

[![Coverage Status](https://coveralls.io/repos/SimonDanisch/Sugar.jl/badge.svg?branch=master&service=github)](https://coveralls.io/github/SimonDanisch/Sugar.jl?branch=master)

[![codecov.io](http://codecov.io/github/SimonDanisch/Sugar.jl/coverage.svg?branch=master)](http://codecov.io/github/SimonDanisch/Sugar.jl?branch=master)



Library for working with ASTs, Lambdas and lowered code.

Most important function:

```Julia
using Sugar

function controlflow_1(a, b)
    if a == 10
        x = if b == 22
            7
        else
            8
        end
        for i=1:100
            x += i
            x -= 77
            if i == 77
                continue
            elseif i == 99
                break
            end
        end
        return x
    else
        return 77
    end
end

Sugar.sugared(controlflow_1, (Int, Int), code_lowered)
```
This will return:

```Julia
quote
    NewvarNode(:(_4))
    if _2 == 10
        if _3 == 22
            _7 = 7
        else
            _7 = 8
        end
        _4 = _7
        SSAValue(0) = (Main.colon)(1,100)
        _5 = (Base.start)(SSAValue(0))
        while !((Base.done)(SSAValue(0),_5))
            SSAValue(1) = (Base.next)(SSAValue(0),_5)
            _6 = (Core.getfield)(SSAValue(1),1)
            _5 = (Core.getfield)(SSAValue(1),2)
            _4 = _4 + _6
            _4 = _4 - 77
            if _6 == 77
                continue
            end
            if _6 == 99
                break
            end
        end
        return _4
    end
    return 77
end
```
There are all sorts of functions to e.g. remove the Slots etc.
More documentation for other functionality will follow!

Installation:

```Julia
Pkg.add("Sugar")
```
