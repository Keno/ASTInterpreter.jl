using AbstractTrees

import AbstractTrees: children, printnode

function children(x::Expr)
    x.args
end

pretty_repr(x) = (string(x), :default)
pretty_repr(x::LineNumberNode) = (string(x.file, ": ", x.line), :red)
function pretty_repr(x::Expr)
    if x.head == :body
        ("Body", :blue)
    elseif x.head == :return
        ("Return", :green)
    elseif x.head == :call
        ("Call", :yellow)
    else
        return (repr(x), :default)
    end
end


function printnode(io::IO, x::Union{Expr, LineNumberNode}, color = :default)
    x = pretty_repr(x)
    if color == :default
        color = x[2]
    end
    if color == :default
        print(io, x[1])
    else
        print_with_color(color, io, x[1])
    end
end

# EvaluationTree

immutable Environment
    locals::Dict{Symbol, Any}
    sparams::Dict{Symbol, Any}
end


type Interpreter
    env::Environment
    ast::Any
    it::Any
    cur_state::Any
    next_expr::Any
    shadowtree::Any
    retval::Any
end


#=
function compute_next_cmd(interpreter)
    stmt = interpreter.current_stmt
    if !isa(stmt, Expr)
        interpreter.next_cmd = stmt
        return
    end
    if stmt.head == :call
        push!(expr_stack, stmt)
        interpreter.arg_idx = 2
        interpreter.current_stmt = stmt.args[interpreter.arg_idx]
        compute_next_cmd(interpreter)
    end
end

function enter(ast, args)
    ast = Base.uncompressed_ast(ast)
    code = ast.args[3]
    locals = Dict{Symbol, Any}()
    merge!(locals, args)
    Interpreter(Environment(locals), ast, code.args, Array(Any, 0), 0, code.args[1], nothing)
end

function status(interpreter)
    println("About to run:", interpreter.next_cmd)
end
=#
