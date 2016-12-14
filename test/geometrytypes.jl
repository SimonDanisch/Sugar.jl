using GeometryTypes
using Sugar, MacroTools

@inline function staggered_velocity(velocity, point, d, gs, res)
    p   = (%).(Vec(point), gs)
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

    return Point3f0(
        (1 - w1) .* ((1 - w2) .* v0 + w2 .* pp) +
        w1 .* ((1 - w2) .* pp2 + w2 .* vn)
    )
end

f = staggered_velocity
types = (Array{Vec3f0, 3}, Point3f0, Vec3f0, Vec{3, Int}, Vec{3, Int})

ast = Sugar.clean_typed(staggered_velocity, types)
