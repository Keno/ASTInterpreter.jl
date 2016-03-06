# Location-preserving lowering for some of julia AST to improve quality of
# matching for the AST Interpreter

import JuliaParser: Lexer
import JuliaParser.Lexer: ¬, ⨳, ⪥, SourceExpr

function do_lowering(ex)
    isa(¬ex, Expr) || return ex
    if (¬ex).head == :typed_vcat
        if any(x->isexpr(x,:row), (¬ex).args)
            # TODO: Make this a split source range
            transformed_ex = ⨳(:call,SourceExpr(TopNode(:typed_hvcat),SourceRange()),first(children(ex)))
            ncols = length((¬ex).args[2].args) # Number of columns in the first row
            nrows = length((¬ex).args) - 1     # -1 for the type
            transformed_ex = transformed_ex ⪥ (SourceExpr((ncols,nrows),SourceRange()),)
            for nex in drop(children(ex),1)
                @assert (¬nex).head == :row
                transformed_ex = transformed_ex ⪥ nex
            end
        else
            transformed_ex = ⨳(:call,SourceExpr(TopNode(:typed_vcat),SourceRange())) ⪥ ex
        end
        transformed_ex
    elseif (¬ex).head == :(:)
        transformed_ex = ⨳(:call,SourceExpr(TopNode(:colon),SourceRange())) ⪥ ex
        transformed_ex
    elseif (¬ex).head == :(.)
        transformed_ex = ⨳(:call,SourceExpr(TopNode(:getfield),SourceRange())) ⪥ ex
        transformed_ex
    elseif (¬ex).head == :ref
        transformed_ex = ⨳(:call,SourceExpr(TopNode(:getindex),SourceRange())) ⪥ ex
        transformed_ex
    elseif (¬ex).head == :string
        transformed_ex = ⨳(:call,SourceExpr(TopNode(:string),SourceRange())) ⪥ ex
        transformed_ex
    elseif (¬ex).head == :comparison
        @assert length((¬ex).args) == 3
        cs = collect(children(ex))
        transformed_ex = ⨳(:call,cs[2],cs[1],cs[3])
    elseif (¬ex).head == :(+=)
        ⨳(:(=), SourceExpr((¬ex).args[1],SourceRange()), (⨳(:call, SourceExpr(:+,SourceRange())) ⪥ ex))
    elseif (¬ex).head == :tuple
        transformed_ex = ⨳(:call,SourceExpr(TopNode(:tuple),SourceRange())) ⪥ ex
        transformed_ex
    else
        ex
    end
end

function lower!(ex)
    treemap!(do_lowering,PreOrderDFS(ex))
end
