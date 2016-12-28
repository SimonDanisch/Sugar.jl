using Sugar, StaticArrays, GeometryTypes
typealias Vec3f0 SVector{3, Float32}
typealias Vec SVector

function staggered_velocity(velocity, point, d, gs, res)
    p   = (%).(point, gs)
    i   = Vec{3, Int}(floor.(p ./ d) + 1)
    ip  = (%).(i, res) + 1

    v0  = velocity[i[1], i[2], i[3]]

    pxp = velocity[ip[1], i[2], i[3]]
    pyp = velocity[i[1], ip[2], i[3]]
    pzp = velocity[i[1], i[2], ip[3]]

    vn = Vec3f0(
        velocity[i[1], ip[2], ip[3]][1],
        velocity[ip[1], i[2], ip[3]][2],
        velocity[ip[1], ip[2], i[3]][3]
    )
    pp  = Vec3f0(pyp[1], pxp[2], pxp[3])
    pp2 = Vec3f0(pzp[1], pzp[2], pyp[3])

    w   = p - (i - 1) .* d
    w1  = Vec3f0(w[3], w[3], w[2])
    w2  = Vec3f0(w[2], w[1], w[1])

    return Vec3f0(
        (1 - w1) .* ((1 - w2) .* v0 + w2 .* pp) +
        w1 .* ((1 - w2) .* pp2 + w2 .* vn)
    )
end
function staggered_advect!(particle, velocity, dt, d, res, gridsize)
    map!(particle) do p

        k1 = staggered_velocity(velocity, p, d, gridsize, res)

        k2 = p + k1 .* dt * 0.5f0
        k2 = staggered_velocity(velocity, k2, d, gridsize, res)

        k3 = p + k2 .* dt * 0.5f0
        k3 = staggered_velocity(velocity, k3, d, gridsize, res)

        k4 = p + k3 .* dt
        k4 = staggered_velocity(velocity, k4, d, gridsize, res)

        p .+ dt/6f0 .* (k1 .+ 2f0*k2 .+ 2f0*k3 .+ k4)
    end
end



vals = (
    rand(Point3f0, 10),
    rand(Vec3f0, 10, 10, 10),
    1f0,
    Vec3f0(0.5, 0.5, 0.5),
    Vec(10, 10, 10),
    Vec(10, 10, 10),
)
staggered_advect!(vals...)
xmacro, str = Sugar.macro_form(staggered_advect!, map(typeof, vals))
x = Sugar.get_ast(code_lowered, staggered_advect!, map(typeof, vals))
lam = Sugar.get_lambda(code_typed, staggered_advect!, map(typeof, vals))
test = sugared(staggered_advect!, map(typeof, vals), code_typed)
test.args[1].args[2].args[1].args[2:end]


body = Sugar.normalize_ast(test)[1]
slots = Sugar.slot_vector(Sugar.get_lambda(code_typed, staggered_advect!, map(typeof, vals)))
sd = Dict(slots)
f = body.args[3].args[1]
typs = map(x->sd[x][2], f.args[2:end])
fun = f.args[1]
func = Sugar.get_func(fun)
types = (typs[[1, 2, 2]]...)
ast = Sugar.sugared(func, types)
slots = Sugar.slot_vector(Sugar.get_lambda(code_typed, func, types))
sd = Dict(slots)

function myImg7(pts::Integer)
    # rotation of ellipse
    aEll = 35.0/180.0*pi
    axes_inv = [6.0, 25.0]
    values = collect(linspace(-0.5,0.5,pts))

    img = zeros(Float64, pts, pts)
    cosa = cos(aEll)
    sina = sin(aEll)
    @inbounds @fastmath for j in eachindex(values)
        @simd for i in eachindex(values)
            Xr = cosa*values[i] - sina*values[j]
            Yr = cosa*values[j] + sina*values[i]
            v = (axes_inv[1] * Xr^2 + axes_inv[2] * Yr^2)
            k = v <= 1.0 ? 10.0*pi*Yr : 0.0
            img[i,j] = mod(k-pi, 2*pi) + pi
        end
    end
    return img
end
ast = Sugar.sugared(myImg7, (Int,), code_typed)


body = Expr(:body); body.args = ast.args
body.typ = Sugar.return_type(myImg7, (Int,))
# Fix slot names and types in function body
io = STDOUT
li = get_lambda(code_typed, myImg7, (Int,))
ast2 = Sugar.get_ast(code_typed, myImg7, (Int,))
slotnames = Base.lambdainfo_slotnames(li)
@which Base.show_unquoted(
    IOContext(
        IOContext(io, :LAMBDAINFO => li),
        :LAMBDA_SLOTNAMES => slotnames
    ),
    body, 2, 0
)
