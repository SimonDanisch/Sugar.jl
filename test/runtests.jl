using Sugar
using Base.Test


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
