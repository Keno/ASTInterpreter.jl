function _precompile_()
    ccall(:jl_generating_output, Cint, ()) == 1 || return nothing
    # Make sure to exercise the interpreter
    interp = ASTInterpreter.enter_call_expr(nothing,Expr(:call, Base.gcd, 21,  7))
    ASTInterpreter.finish!(interp, recursive=true)
    precompile(ASTInterpreter.RunDebugREPL,(ASTInterpreter.Interpreter,))
    nothing
end
