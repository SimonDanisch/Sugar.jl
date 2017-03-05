import Base: indent_width, quoted_syms, uni_ops, expr_infix_wide, expr_infix_any
import Base: all_ops, expr_calls, expr_parens, ExprNode, show_unquoted, show_block
import Base: show_list, show_enclosed_list, operator_precedence, is_linenumber
import Base: is_quoted, is_expr, TypedSlot, ismodulecall, is_intrinsic_expr
import Base: show_generator, show_call


abstract ASTIO <: IO

Base.print(io::ASTIO, args...) = print(io.io, args...)
Base.print(io::ASTIO, arg::String) = print(io.io, arg)
Base.print(io::ASTIO, arg::Char) = print(io.io, arg)
Base.print(io::ASTIO, arg::Symbol) = print(io.io, arg)
Base.write(io::ASTIO, args...) = write(io.io, args...)
Base.write(io::ASTIO, arg::UInt8) = write(io.io, arg)
Base.write(io::ASTIO, arg::String) = write(io.io, arg)
Base.write(io::ASTIO, arg::Char) = write(io.io, arg)

immutable ExprNotSupported
    message::String
    line::Int
end

unsupported_expr(message, line) = throw(ExprNotSupported(message, line))


get_type(io::ASTIO, x::Expr) = x.typ
get_type{T}(io::ASTIO, x::Type{T}) = Type{T}
get_type{T}(io::ASTIO, x::T) = T
get_type(io::ASTIO, x::GlobalRef) = typeof(eval(x))
get_type(io::ASTIO, slot::Slot) = get_slottypename(io, slot)[1]
function get_type(io::ASTIO, slot::SSAValue)
    li = io.lambdainfo
    #if isa(li, LambdaInfo)
        ssatypes = li.ssavaluetypes
        return ssatypes[slot.id + 1]
    #end
    error("What's up with dat LambdaInfo? $slot, $li")
end

function get_slottypename(io::ASTIO, ex)
    typ = isa(ex, TypedSlot) ? ex.typ : Any
    slotid = ex.id
    li = getcodeinfo!(io.method)
    #if isa(li, LambdaInfo)
        slottypes = li.slottypes
        if isa(slottypes, Array) && slotid <= length(slottypes::Array)
            slottype = slottypes[slotid]
            # The Slot in assignment can somehow have an Any type
            slottype <: typ && (typ = slottype)
        end
    #end
    slotnames = io.slotnames
    name = if (isa(slotnames, Vector{String}) &&
        slotid <= length(slotnames::Vector{String}))
        (slotnames::Vector{String})[slotid]
    else
        string("_", slotid)
    end
    typ, name
end

ssavalue_name(ssa::SSAValue) = string("_ssavalue_", ssa.id)

# function Base.show_unquoted(io::ASTIO, ssa::SSAValue, ::Int, ::Int)
#     print(io, ssavalue_name(ssa))
# end
