using ASTInterpreter

struct DummyState; end
Base.LineEdit.transition(s::DummyState, _) = nothing
dummy_state(interp) = ASTInterpreter.InterpreterState(interp, interp, 1, DummyState(), nothing, nothing)

# Steps through the whole expression using `s`
function step_through(interp)
    state = dummy_state(interp)
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
state = dummy_state(interp)

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

# Optional arguments
function optional(n = sin(1))
    x = asin(n)
    cos(x)
end

interp = ASTInterpreter.enter_call_expr(nothing, :($(optional)()))
state = dummy_state(interp)
# First call steps in
ASTInterpreter.execute_command(state, state.top_interp, Val{:n}(), "n")
@assert interp.retval == nothing
# cos(1.0)
ASTInterpreter.execute_command(state, state.top_interp, Val{:n}(), "n")
@assert interp.retval == nothing
# return
ASTInterpreter.execute_command(state, state.top_interp, Val{:n}(), "n")
@assert interp.retval == cos(1.0)

# Macros
macro insert_some_calls()
    esc(quote
        x = sin(b)
        y = asin(x)
        z = sin(y)
    end)
end

# Work around the fact that we can't detect macro expansions if the macro
# is defined in the same file
include_string("""
function test_macro()
    a = sin(5)
    b = asin(a)
    @insert_some_calls
    z
end
""","file.jl")

interp = ASTInterpreter.enter_call_expr(nothing, :($(test_macro)()))
state = dummy_state(interp)
# a = sin(5)
ASTInterpreter.execute_command(state, state.top_interp, Val{:n}(), "n")
@assert interp.retval == nothing
# b = asin(5)
ASTInterpreter.execute_command(state, state.top_interp, Val{:n}(), "n")
@assert interp.retval == nothing
# @insert_some_calls
ASTInterpreter.execute_command(state, state.top_interp, Val{:n}(), "n")
@assert interp.retval == nothing
# return z
ASTInterpreter.execute_command(state, state.top_interp, Val{:n}(), "n")
@assert interp.retval == sin(5)

# Test stepping into functions with keyword arguments
f(x; b = 1) = x+b
g() = f(1; b = 2)
interp = ASTInterpreter.enter_call_expr(nothing, :($(g)()));
state = dummy_state(interp)
# Step to the actual call - TODO: We may want to hide these
ASTInterpreter.execute_command(state, state.top_interp, Val{:nc}(), "nc")
ASTInterpreter.execute_command(state, state.top_interp, Val{:nc}(), "nc")
ASTInterpreter.execute_command(state, state.top_interp, Val{:nc}(), "nc")
# Step in
ASTInterpreter.execute_command(state, state.top_interp, Val{:s}(), "s")
@assert state.top_interp.next_expr[2] == :(($+)(1,2))
# Should get out in two steps
ASTInterpreter.execute_command(state, state.top_interp, Val{:finish}(), "finish")
ASTInterpreter.execute_command(state, state.top_interp, Val{:finish}(), "finish")
@assert interp.retval == 3
