using ASTInterpreter

# Simple evaling of function argument
function evalfoo1(x,y)
    x+y
end
interp = ASTInterpreter.enter_call_expr(nothing, :($(evalfoo1)(1,2)))
state = dummy_state(interp)
ok, res = ASTInterpreter.eval_code(state, "x")
@assert res == 1

ok, res = ASTInterpreter.eval_code(state, "y")
@assert res == 2

# Evaling with sparams
function evalsparams{T}(x::T)
    x
end
interp = ASTInterpreter.enter_call_expr(nothing, :($(evalsparams)(1)))
state = dummy_state(interp)
ok, res = ASTInterpreter.eval_code(state, "x")
@assert res == 1

ok, res = ASTInterpreter.eval_code(state, "T")
@assert res == Int
