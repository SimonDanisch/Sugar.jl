# Helper for writing an AST to a string! Extended by e.g. Transpiler!

@compat abstract type ASTIO <: IO end

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
ssavalue_name(ssa::SSAValue) = string("_ssavalue_", ssa.id)
