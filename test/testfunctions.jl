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

function staticparams_1{T1 <: Integer, T2}(a::T1, b::T2)
    x = if T2 <: Number
        T1(b)
    else
        one(T1)
    end
    f = rand(T2)
    f * x
end

"""
Will docs disturb macro_form's file/string based method to get source
"""
staticparams_short{T, T2}(a::T, b::T2) = a + b

#comment to test if this annoys macro_form file/string based method to get source
function static_annon{T}(a::T, b)
    c = a+b::T
    if c == 10
        for i=1:7
            c += rand(Bool) ? 1 : 2
        end
    end
    f = (x,y) -> (x::T)^y
    c, f
end
