# Location-preserving lowering for some of julia AST to improve quality of
# matching for the AST Interpreter

import JuliaParser: Lexer
import JuliaParser.Tokens: ¬, ⨳, ⪥, SourceExpr

function do_lowering(ex)
    isa(¬ex, Expr) || return ex
    if (¬ex).head == :typed_vcat
        if any(x->isexpr(x,:row), (¬ex).args)
            # TODO: Make this a split source range
            transformed_ex = ⨳(:call,TopNode(:typed_hvcat)⤄ex,first(children(ex)))
            ncols = length((¬ex).args[2].args) # Number of columns in the first row
            nrows = length((¬ex).args) - 1     # -1 for the type
            transformed_ex = transformed_ex ⪥ ((ncols,nrows)⤄ex,)
            for nex in drop(children(ex),1)
                @assert (¬nex).head == :row
                transformed_ex = transformed_ex ⪥ nex
            end
        else
            transformed_ex = ⨳(:call,TopNode(:typed_vcat)⤄ex) ⪥ ex
        end
        transformed_ex
    elseif (¬ex).head == :(:)
        transformed_ex = ⨳(:call,TopNode(:colon)⤄ex) ⪥ ex
        transformed_ex
    elseif (¬ex).head == :(.)
        transformed_ex = ⨳(:call,TopNode(:getfield)⤄ex) ⪥ ex
        transformed_ex
    elseif (¬ex).head == :ref
        ex = treemap!(PreOrderDFS(ex)) do s
            !isa(¬s, Symbol) && return s
            ¬s == :end ? ⨳(:call,TopNode(:endof)⤄s,copy(collect(children(ex))[1])) : s
        end
        transformed_ex = ⨳(:call,TopNode(:getindex)⤄ex) ⪥ ex
        transformed_ex
    elseif (¬ex).head == :string
        transformed_ex = ⨳(:call,TopNode(:string)⤄ex) ⪥ ex
        transformed_ex
    elseif (¬ex).head == :comparison
        @assert length((¬ex).args) == 3
        cs = collect(children(ex))
        transformed_ex = ⨳(:call,cs[2],cs[1],cs[3])
    elseif (¬ex).head == :(+=)
        ⨳(:(=), collect(children(ex))[1], (⨳(:call, :+⤄ex) ⪥ ex))
    elseif (¬ex).head == :tuple
        transformed_ex = ⨳(:call,TopNode(:tuple)⤄ex) ⪥ ex
        transformed_ex
    else
        ex
    end
end

function lower!(ex)
    ex = treemap!(do_lowering,PreOrderDFS(ex))
end
