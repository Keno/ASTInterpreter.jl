eval(Base,:(have_color = true))
using ASTInterpreter
using Base.Test

# Properly handle `call`
function CallTest()
    UnitRange{Int64}(2,2)
end

interp = enter(CallTest, Environment())
@test ASTInterpreter.finish!(interp; print_step = false, recursive=true) == CallTest()

# Properly handle :meta annotations
function MetaTest()
    @Base._pure_meta
    0
end

interp = enter(MetaTest, Environment())
@test ASTInterpreter.finish!(interp; print_step = false, recursive=true) == MetaTest()

# Test Vararg handling
function VATest(x...)
    x
end
callVA() = VATest()

interp = enter(callVA, Environment())
@test ASTInterpreter.finish!(interp; print_step = false, recursive=true) == callVA()

# Test Loops
function LoopTest()
    x = Int[]
    for i = 1:2
        push!(x, i)
    end
    x
end

interp = enter(LoopTest, Environment())
@test ASTInterpreter.finish!(interp; print_step = false, recursive=true) == LoopTest()

# Test Loops
function ContinueTest()
    x = Int[]
    for i = 1:3
        if true
            push!(x, i)
            continue
        end
        error("Fell through")
    end
    x
end

interp = enter(ContinueTest, Environment())
@test ASTInterpreter.finish!(interp; print_step = false, recursive=true) == ContinueTest()

#foo() = 1+1
function foo(n)
    x = n+1
    ((BigInt[1 1; 1 0])^x)[2,1]
end


interp = enter(foo, Environment(Dict(:n => 20),Dict{Symbol,Any}()))
#@test ASTInterpreter.finish!(interp; print_step = false, recursive=true) == foo(20)
