using ASTInterpreter

immutable DummyState; end
Base.LineEdit.transition(s::DummyState, _) = nothing

# Steps through the whole expression using `s`
function step_through(interp)
    state = ASTInterpreter.InterpreterState(interp, interp, 1, DummyState())
    while !(isa(interp.next_expr[2], Expr) && interp.next_expr[2].head == :return)
        ASTInterpreter.execute_command(state, interp, Val{:s}(), "s")
    end
    return interp.retval
end

@assert step_through(ASTInterpreter.enter_call_expr(nothing, :($(+)(1,2.5)))) == 3.5
@assert step_through(ASTInterpreter.enter_call_expr(nothing, :($(sin)(1)))) == sin(1)

# Step into generated functions
@generated function generatedfoo(T)
    :(return $T)
end
callgenerated() = generatedfoo(1)
interp = ASTInterpreter.enter_call_expr(nothing, :($(callgenerated)()))
state = ASTInterpreter.InterpreterState(interp, interp, 1, DummyState())

# Step into the generated function itself
ASTInterpreter.execute_command(state, state.top_interp, Val{:sg}(), "sg")

# Should now be in generated function
interp = state.interp
ASTInterpreter.execute_command(state, state.top_interp, Val{:finish}(), "finish")
@assert interp.retval == :(return $(Int64))

# Now finish the regular function
interp = state.interp
ASTInterpreter.execute_command(state, state.top_interp, Val{:finish}(), "finish")
@assert interp.retval == Int64

