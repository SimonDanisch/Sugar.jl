using Sugar: LazyMethod
using Transpiler: CLMethod
using Iterators
using GPUArrays
ctx = CLBackend.init()

f = Transpiler.CLFunction(
    Base._ind2sub, ((2,2,2), 2), ctx.queue
)

f, gltypes = Base._ind2sub, map(typeof, ((2,2,2), 2))
decl = CLMethod((f, gltypes))
funcsource = Sugar.getast!(decl)

for elem in funcsource.args[end].args[1].expressions
    println(elem)
end


tuple((int)((ind - l * indnext) + f)[1], _ind2sub_4(tail_2(inds), indnext)[1], _ind2sub_4(tail_2(inds), indnext)[2])

(tuple)(
    tuple((_3 - (_7 * _5)) + _6)[1],
    _ind2sub(tail(_2), _5)[1],
    _ind2sub(tail(_2), _5)[2]
)

tuple((+)((-)(_3, (*)(_7, _5)), _6))

tuple(
(int)((ind - l * indnext) + f)[1],
_ind2sub_4(tail_2(inds), indnext)[1],
_ind2sub_4(tail_2(inds), indnext)[2]
)
