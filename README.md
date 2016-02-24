# ASTInterpreter

[![Build Status](https://travis-ci.org/Keno/ASTInterpreter.jl.svg?branch=master)](https://travis-ci.org/Keno/ASTInterpreter.jl)

The AST Interpreter component of Gallium (i.e. does not include any breakpoint,
  stuff, etc.). This is a development prototype and comes with it's own debug
  prompt for that purpose.
  
Usage:
```
using ASTInterpreter

function foo(n)
    x = n+1
    ((BigInt[1 1; 1 0])^x)[2,1]
end

interp = enter(foo, Environment(Dict(:n => 20),Dict{Symbol,Any}()))
ASTInterpreter.RunDebugREPL(interp)
```
Commands:
- `n` steps to the next statement
- `s` steps to the next expression and into calls
- blank steps to the next expression but skips calls
- `bt` shows a simple backtrace
- ``` `stuff ``` runs `stuff` in the current frame's context

This is a prototype, do not expect it to be correct or usable.

#### Current Dependencies

```julia
Pkg.checkout("Reactive")
Pkg.checkout("JuliaParser", "kf/loctrack")
Pkg.clone("https://github.com/Keno/TerminalUI.jl.git")
Pkg.clone("https://github.com/Keno/VT100.jl.git")
Pkg.clone("https://github.com/Keno/AbstractTrees.jl.git")
Pkg.clone("https://github.com/Keno/LineNumbers.jl.git")
```
