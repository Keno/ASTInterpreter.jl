using ASTInterpreter

function foo(n)
    x = n+1
    ((BigInt[1 1; 1 0])^x)[2,1]
end

interp = enter(foo, Environment(Dict(:n => 20),Dict{Symbol,Any}()))
ASTInterpreter.RunDebugREPL(interp)
