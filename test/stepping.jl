using ASTInterpreter

# Steps through the whole expression using `s`
function step_through(interp)
    state = ASTInterpreter.InterpreterState(interp, interp, 1, nothing)
    while !(isa(interp.next_expr[2], Expr) && interp.next_expr[2].head == :return)
        ASTInterpreter.execute_command(state, interp, Val{:s}(), "s")
    end
    return interp.retval
end

@assert step_through(ASTInterpreter.enter_call_expr(nothing, :($(+)(1,2.5)))) == 3.5
@assert step_through(ASTInterpreter.enter_call_expr(nothing, :($(sin)(1)))) == sin(1)
