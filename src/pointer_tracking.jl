using Sugar
using Sugar: replace_expr, expr_type, resolve_func, to_tuple, LazyMethod
"""
Interface to indicate that a type needs tracking.
"""
is_tracked_type(m, T) = false

"""
Figures out if a type `T` contains any type for which `is_tracked_type` returns true.
Returns if it contains a tracked type and the fields with the types in the form of:
`[(field1, nested_field, tracked_field)]`
"""
function contains_tracked_type(
        m,
        ::Type{T},
        parent_field = (),
        trackedfields = []
    ) where T
    has_tracked_field = false
    for fname in fieldnames(T)
        FT = fieldtype(T, fname)
        if is_tracked_type(m, FT)
            has_tracked_field = true
            push!(trackedfields, (parent_field..., fname))
        else
            _has_tracked_field, trackedfields = contains_tracked_type(m, FT, (fname,), trackedfields)
            has_tracked_field |= _has_tracked_field
        end
    end
    has_tracked_field, trackedfields
end

needs_tracking(m, ::Type{T}) where T = contains_tracked_type(m, T)[1] || is_tracked_type(m, T)

track_types!(m, any, pointer_map) = pointer_map

get_fields_type(T, fields::NTuple{1}) = fieldtype(T, first(fields))
get_fields_type(T, fields::NTuple{N}) where N = get_fields_type(fieldtype(T, first(fields)), Base.tail(fields))

get_fields(x, fields::NTuple{1}) = getfield(x, first(fields))
get_fields(x, fields::NTuple{N}) where N = get_fields(getfield(x, first(fields)), Base.tail(fields))


function track_types!(m, args::Vector, pointer_map)
    for elem in args
        track_types!(m, elem, pointer_map)
    end
    pointer_map
end

push_app!(vec, elem) = push!(vec, elem)
push_app!(vec, elem::Vector) = append!(vec, elem)
"""
Tracks a type for which `is_tracked_type` returns true, even across functions.
"""
function track_types!(m, expr::Expr, pointer_map)
    head, args = expr.head, expr.args
    if head === :new
        # Constructors, tracking it's argument pointers
        f_args = @view args[2:end]
        ptrs = []
        typ = args[1]
        for i = 1:length(f_args)
            arg = f_args[i]
            fname = fieldname(typ, i)
            track_types!(m, arg, pointer_map)
            T = expr_type(m, arg)
            if needs_tracking(m, T) && haskey(pointer_map, arg)
                push_app!(ptrs, map(pointer_map[arg]) do ptr
                    # append the field name
                    (fname, ptr...)
                end)
            end
        end
        pointer_map[expr] = ptrs
    elseif head in (:call, :curly) # curly and call are both call like
        f_args = @view args[2:end]
        args_need_tracking = true
        ptrs = []
        trackers = Dict()
        @assert isa(args[1], LazyMethod)
        f = resolve_func(m, args[1])
        m2 = args[1]
        for i = 1:length(f_args)
            arg = f_args[i]
            T = expr_type(m, arg)
            track_types!(m, arg, pointer_map)
            haskey(pointer_map, arg) && push_app!(ptrs, pointer_map[arg])
            trackers[TypedSlot(i + 1, T)] = get(pointer_map, arg, :failed_tracking)
        end
        m2.cache[:tracked_types] = trackers
        track_types!(m2, getast!(m2), trackers)

        if isa(f, DataType) && f <: Tuple
            # Tuples need special treatment since the constructor is intrinsic without using new
            pointer_map[expr] = map(enumerate(ptrs)) do i_arg
                i, arg = i_arg
                (Symbol("field$i"), arg...)
            end
        elseif f == getfield
            # getfield is special, since that's how we get pointers out of structs
            field = args[3]
            @assert length(ptrs) >= 1
            newfields = []
            for fields in ptrs
                if isa(fields, Tuple) && !isempty(fields) && first(fields) == field
                    # pop the head field, since getfield gets it out of the struct
                    push!(newfields, Base.tail(fields))
                end
            end
            pointer_map[expr] = newfields
        end
        if haskey(trackers, m2) # returns type with ptr
            pointer_map[expr] = trackers[m2]
        end
    elseif head === :(=)
        lhs, rhs = args
        if needs_tracking(m, expr_type(m, lhs))
            track_types!(m, rhs, pointer_map)
            pointer_map[lhs] = get(pointer_map, rhs, :rhs_fail)
        end
    elseif head === :return && length(args) == 1
        arg = args[1]
        track_types!(m, arg, pointer_map)
        if needs_tracking(m, expr_type(m, arg))
            ret = get(pointer_map, arg, :return_fail)
            pointer_map[m] = ret
        end
    else
        track_types!(m, args, pointer_map)
    end
    pointer_map
end



function track_types!(m::LazyMethod)
    args = to_tuple(m.signature[2])
    pointer_map = Dict()
    for i = 1:length(args)
        T = args[i]
        needs_tracking, fields = contains_tracked_type(m, T)
        if needs_tracking
            slot = TypedSlot(i + 1, T)
            name = Sugar.slotname(m, slot)
            unique_ptrs = map(enumerate(fields)) do i_field
                (i_field[2]..., gensym(Symbol(string(name, i_field[1]))))
            end
            pointer_map[slot] = unique_ptrs
        end
    end
    track_types!(m, getast!(m), pointer_map)
    m.cache[:tracked_types] = pointer_map
    return
end
