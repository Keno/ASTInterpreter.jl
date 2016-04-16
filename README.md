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
Basic Commands:
- `n` steps to the line
- `s` steps into the next call
- `finish` runs to the end of the function
- `bt` shows a simple backtrace
- ``` `stuff ``` runs `stuff` in the current frame's context
- `fr v` will show all variables in the current frame
- `f n` where `n` is an integer, will go to the `n`-th frame.

Advanced commands:
- `nc` steps to the next call
- `ns` steps to the next statement
- `se` does one expression step
- `si` does the same but steps into a call if a call is the next expression
- `shadow` shows the internal representation of the expression tree (for debugger debugging only)
- `loc` shows the column data for the current top frame, in the same format
  as JuliaParsers's testshell.


This is a prototype, do not expect it to be correct or usable.

# Experimental mode

There is an experimental UI mode accessible by setting `ASTInterpreter.fancy_mode = true`, which attempts to provide a better interface but is not currently not capable of handling all julia code. Use at your own peril.

#### Current Dependencies

```julia
Pkg.clone("https://github.com/JuliaLang/Reactive.jl.git")
Pkg.clone("https://github.com/JuliaLang/JuliaParser.jl.git")
Pkg.clone("https://github.com/Keno/TerminalUI.jl.git")
Pkg.clone("https://github.com/Keno/VT100.jl.git")
Pkg.clone("https://github.com/Keno/AbstractTrees.jl.git")
Pkg.clone("https://github.com/Keno/LineNumbers.jl.git")
Pkg.clone("https://github.com/Keno/ASTInterpreter.jl.git")
```
