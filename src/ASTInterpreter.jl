module ASTInterpreter

export enter, Environment, @enter
import Base: LineEdit, REPL

using AbstractTrees
using JuliaParser
using JuliaParser.Lexer
using Base.Meta
import JuliaParser.Lexer: SourceNode, SourceRange

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
    gensyms::Dict{Int, Any}
end
Environment() = Environment(Dict{Symbol,Any}(),Dict{Symbol,Any}())
Environment(locals,sparams) = Environment(locals,sparams,Dict{Int,Any}())

type Interpreter
    parent::Nullable{Interpreter}
    env::Environment
    meth::Any
    ast::Any
    it::Any
    cur_state::Any
    next_expr::Any
    shadowtree::Any
    code::AbstractString
    loctree::Any
    retval::Any
end

function make_shadowtree(tree)
    resulttree = copy(tree)
    annotations = AbstractTrees.make_annotations(resulttree, false) do node, parent_ev
        if parent_ev
            return parent_ev
        end
        unevaluated = isa(node, Expr) || isa(node, GlobalRef) || isa(node, Symbol) ||
            isa(node,GenSym) || isa(node, GotoNode) || isa(node, QuoteNode)
        if isa(node, Expr) && (node.head == :meta || node.head == :boundscheck ||
            node.head == :inbounds)
            unevaluated = false
        end
        !unevaluated
    end
    shadowtree = AbstractTrees.ShadowTree(Tree(resulttree), Tree(annotations)) 
    it = filter(x->!isa(x[2],LineNumberNode),indenumerate(PostOrderDFS(resulttree)))
    shadowtree, it   
end

function enter(meth, tree::Expr, env, parent = Nullable{Interpreter}(); loctree = nothing, code = "")
    shadowtree, it = make_shadowtree(tree)
    
    interp = Interpreter(Nullable{Interpreter}(parent), env, meth, tree, it,
        start(it), nothing, shadowtree, code, loctree, nothing)
    ind, node = next_expr!(interp)
    while interp.shadowtree.shadow[ind].val
        ind, node = next_expr!(interp)
    end
    interp
end
function enter(meth::Method, env::Environment, parent = Nullable{Interpreter}(); kwargs...)
    ast = Base.uncompressed_ast(meth.func.code)
    tree = ast.args[3]
    enter(meth, tree, env, parent; kwargs...)
end
enter(f::Function, env) = enter(first(methods(f)), env)

function print_shadowtree(shadowtree, highlight = nothing, inds = nothing)
    from = nothing
    to = nothing
    if inds !== nothing
        from = first(inds)
        to = last(inds)
    end
    AbstractTrees.print_tree(STDOUT, shadowtree, withinds = true, from = from, to = to) do io, annotatednode, inds
        node, evaluated = annotatednode.tree.x, annotatednode.shadow.x.val
        str, _ = pretty_repr(node)
        print_with_color((inds == highlight) ? :yellow : (evaluated ? :green : :red), io, str)
    end
end

function node_repr(x)
    isa(x,GlobalRef) ? string(x.mod,'.',x.name) : string(x)
end

function print_status(interp, highlight = nothing)
    if interp.loctree === nothing
        print_shadowtree(interp.shadowtree, highlight)
    else
        union = reduce(⤄,PostOrderDFS(interp.loctree))
        file = SourceFile(interp.code)    
        startline = compute_line(file, union.offset+1)
        stopline = compute_line(file, union.offset+union.length+1)
        if highlight != nothing
            locnode = Tree(interp.loctree)[highlight].loc
            offset = locnode.offset
            
            if offset != -1 % UInt32
                offsetline = compute_line(file, offset+1)
                startoffset = max(file.offsets[max(offsetline-3,1)], file.offsets[startline])-1
                stopoffset = endof(interp.code)
                if offsetline + 3 < endof(file.offsets)
                    stopoffset = min(stopoffset, file.offsets[offsetline + 3]-1)
                end
                if stopline + 1 < endof(file.offsets)
                    stopoffset = min(stopoffset, file.offsets[stopline + 1]-1)
                end
                # Algorithm:
                # 1. PostOrderDFS over active shadow tree
                # 2. Collect (range, ind) pairs of evaluated AST nodes
                # 3. Take the completement of the union of all ranges and split
                #    into source ranges.
                # 4. Alternatingly print the original values and the new nodes
                #    depending on which node is earlier.
                ishighlight(x) = length(x[1]) >= length(highlight) && x[1][1:length(highlight)] == highlight
                triples = collect(filter(y->(Lexer.normalize(y[1]) != SourceRange()),
                    map(filter(x->x[2].val && !ishighlight(x),
                    indenumerate(PostOrderDFS(interp.shadowtree.shadow)))) do x
                        loc, val = Tree(interp.loctree)[x[1]],Tree(interp.shadowtree.tree)[x[1]]
                        loc, :green, val
                    end))

                # Special handling for highlight
                if Lexer.normalize(Tree(interp.loctree)[highlight]) != SourceRange()
                    push!(triples,(Tree(interp.loctree)[highlight],:yellow,Tree(interp.shadowtree.tree)[highlight]))
                end
                sort!(triples, by = x->Lexer.normalize(x[1]).offset)

                append!(triples,map(
                    Lexer.sortedcomplement(SourceRange(startoffset,stopoffset-startoffset+1,0),map(x->x[1],triples))) do x
                    off = x.offset
                    (x,:white,interp.code[off+1:(off+x.length)])
                end)
                sort!(triples, by = x->Lexer.normalize(x[1]).offset)
                for piece in triples
                    print_with_color(piece[2],node_repr(piece[3]))
                end
                
                #print_with_color(:white,interp.code[startoffset:offset])
                #h = Tree(interp.shadowtree)[highlight]
                #print_with_color(:yellow,node_repr(h.tree.x))
                #print_with_color(:white,interp.code[(offset+length+1):stopoffset])
                println()
                return
            end
        end
        println(join(map(bytestring,file[startline:stopline]),""))
    end
end

function next_expr!(interp)
    x, next_it = next(interp.it, interp.cur_state)
    interp.cur_state = next_it
    interp.next_expr = x
end

function find_label_index(tree, label)
    for (i, node) in enumerate(tree.args)
        if isa(node, LabelNode) && node.label == label
            return i
        end
    end
    error("Label not found")
end

function goto!(interp, target)
    # Reset shadowtree
    interp.shadowtree, interp.it = make_shadowtree(interp.ast)
    lind = find_label_index(interp.ast, target)
    
    # next_expr! below will move past the label node
    interp.cur_state = next(interp.it,(false,nothing,[lind]))[2]
    return done!(interp)
end

function step_expr(interp)
    ind, node = interp.next_expr

    if isa(node, Expr) && node.head == :return
        interp.retval = node.args[1]
        println("Returning $(node.args[1])")
        return false
    end
    if isa(node, Symbol) || isa(node,GenSym)
        # Check if we're the LHS of an assignment
        if ind[end] == 1 && interp.shadowtree.tree[ind[1:end-1]].head == :(=)
            ret = node
        elseif isa(node,GenSym)
            ret = interp.env.gensyms[node.id]
        else
            ret = haskey(interp.env.locals, node) ?
                interp.env.locals[node] :
                haskey(interp.env.sparams, node) ?
                interp.env.sparams[node] :
                eval(node)
        end
    elseif isa(node, Expr)
        if node.head == :(=)
            lhs = node.args[1]
            rhs = node.args[2]
            if isa(lhs, GenSym)
                interp.env.gensyms[lhs.id] = rhs
            else
                interp.env.locals[lhs] = rhs
            end
            ret = rhs
        elseif node.head == :&
            ret = node
        elseif node.head == :gotoifnot
            ret = node
            if !node.args[1]
                return goto!(interp, node.args[2])
            end
        elseif node.head == :call
            # Don't go through eval since this may have unqouted, symbols and
            # exprs
            f = to_function(node.args[1])
            if isa(f, IntrinsicFunction)
                ret = eval(node)
            else    
                ret = (node.args[2:end]...)
            end
        else
            ret = eval(node)
        end
    elseif isa(node, GotoNode)
        return goto!(interp, node.label)
    elseif isa(node, QuoteNode)
        ret = node.value
    else
        ret = eval(node)
    end
    evaluated!(interp, ret)
end

function next_statement!(interp)
    ind, node = interp.next_expr
    move_past = ind[1]
    while step_expr(interp)
        ind, node = interp.next_expr
        if ind[1] != move_past
            return true
        end
    end
    return false
end

function next_call!(interp)
    ind, node = interp.next_expr
    move_past = ind[1]
    while step_expr(interp)
        ind, node = interp.next_expr
        if isa(node, Expr) && node.head == :call
            return true
        end
    end
    return false
end



function evaluated!(interp, ret)
    ind, node = interp.next_expr
    interp.shadowtree[ind] = (ret, AnnotationNode{Any}(true,AnnotationNode{Any}[]))
    done!(interp)
end

function done!(interp)
    ind, node = next_expr!(interp)
    # Skip evaluated values (e.g. constants)
    while interp.shadowtree.shadow[ind].val
        ind, node = next_expr!(interp)
    end
    return true
end

function to_function(x)
    if isa(x, Function) || isa(x, IntrinsicFunction)
        x
    elseif isa(x, TopNode)
        Base.(x.name)
    else
        x
    end
end

_Typeof(x) = isa(x,Type) ? Type{x} : typeof(x)

function vatuple_name(k::Expr)
    if k.head == :(::) && k.args[2].head == :(...)
        k = k.args[1]
    elseif k.head == :(...)
        k = k.args[1]
    else
        error()
    end
    k
end

function reparse_meth(meth)
    file, line = functionloc(meth)
    contents = open(readall, file)
    buf = IOBuffer(contents)
    for _ in line:-1:2
        readuntil(buf,'\n')
    end
    ts = Lexer.TokenStream{Lexer.SourceLocToken}(buf)
    res = Parser.parse(ts)
    parsedexpr = res.expr
    parsedloc = res.loc
    loweredast = Base.uncompressed_ast(meth.func.code).args[3]
    thecalls = collect(filter(x->isexpr(x[2],:call),indenumerate(PostOrderDFS(parsedexpr))))
    thecalls = thecalls[2:end]
    loctree = treemap(PostOrderDFS(loweredast)) do node, childlocs
        if isexpr(node, :call)
            candidate = shift!(thecalls)
            Tree(parsedloc)[candidate[1]]
        else
            SourceNode(SourceRange(),childlocs)
        end
    end
    loctree, contents
end

function enter_call_expr(interp, expr)
    f = to_function(expr.args[1])
    allargs = expr.args
    callfunc = Base.call
    if is(f,Base._apply)
        f = to_function(allargs[3])
        callfunc = allargs[2]
        if isa(allargs[4],Tuple) && length(allargs) == 4
            allargs = [allargs[3], allargs[4]...]
        else
            allargs = allargs[3:end]
        end
        @show (f,allargs)
    end
    if (!isa(f, IntrinsicFunction) && !isa(f,Function)) || isgeneric(f)
        args = allargs[2:end]
        argtypes = Tuple{map(_Typeof,args)...}
        method = try
            which(f, argtypes)
        catch err
            println(f)
            println(argtypes)
            rethrow(err)
        end
        if !isa(f,Function)
          argtypes = Tuple{_Typeof(f), argtypes.parameters...}
          args = allargs
          f = callfunc
        end
        # Construct the environment from the arguments
        argnames = Base.uncompressed_ast(method.func.code).args[1]
        env = Dict{Symbol,Any}()
        if length(args) < length(argnames) # Empty Vararg
            env[vatuple_name(argnames[end])] = ()
        end
        for (i,(k,v)) in enumerate(zip(argnames, args))
            if isa(k, Expr) # Vararg tuple
                k = vatuple_name(k)
                env[k] = tuple(args[i:end]...)
                break
            end
            env[k] = v
        end
        # Add static parameters to invironment
        (ti, lenv) = ccall(:jl_match_method, Any, (Any, Any, Any),
             argtypes, method.sig, method.tvars)::SimpleVector
        sparams = Dict{Symbol, Any}()
        i = 1
        while i < length(lenv)
            sparams[lenv[i].name] = lenv[i+1]
            i += 2
        end
        loctree, code = reparse_meth(method)
        newinterp = enter(method,Environment(env,sparams),interp, loctree = loctree, code = code)
        return newinterp
    end
    nothing
end

function print_backtrace(interp)
    while true
        println(interp.meth)
        for (name,var) in interp.env.locals
            println("- ",name,"::",typeof(var)," = ",var)
        end
        if isnull(interp.parent)
            break
        end
        interp = get(interp.parent)
    end
end

include(joinpath(dirname(@__FILE__),"..","..","JuliaParser","src","interactiveutil.jl"))

function RunDebugREPL(interp)
    prompt = "debug > "

    repl = Base.active_repl

    # Setup debug panel
    panel = LineEdit.Prompt(prompt;
        prompt_prefix="\e[38;5;166m",
        prompt_suffix=Base.text_colors[:white],
        on_enter = s->true)

    panel.hist = REPL.REPLHistoryProvider(Dict{Symbol,Any}(:debug => panel))

    panel.on_done = (s,buf,ok)->begin
        line = takebuf_string(buf)
        if !ok || strip(line) == "q"
            LineEdit.transition(s, :abort)
        end
        if isempty(strip(line)) && length(panel.hist.history) > 0
            command = panel.hist.history[end]
        else
            command = strip(line)
        end
        if startswith(command, "`")
            body = parse(command[2:end])
            f = Expr(:->,Expr(:tuple,keys(interp.env.locals)...,keys(interp.env.sparams)...),
                body)
            lam = interp.meth.func.code.module.eval(f)
            einterp = enter(nothing,Base.uncompressed_ast(lam.code).args[3],interp.env,interp)
            try
                show(finish!(einterp))
                println(); println()
            catch err
                REPL.display_error(STDERR, err, Base.catch_backtrace())
                REPL.println(STDERR); REPL.println(STDERR)
            end
            return true
        end
        if command == "s"
            expr = interp.next_expr[2]
            if isa(expr, Expr)
                if expr.head == :call
                    x = enter_call_expr(interp, expr)
                    if x !== nothing
                        interp = x
                        print_status(interp, interp.next_expr[1])
                        return true
                    end
                end
            end
        elseif command == "bt"
            print_backtrace(interp)
            println()
            return true
        elseif command == "loc"
            w = create_widget(interp.loctree,interp.code)
            TerminalUI.print_snapshot(TerminalUI.InlineDialog(w,
                Base.Terminals.TTYTerminal("xterm", STDIN, STDOUT, STDERR)
                ))
            return true
        end
        if command == "n" ? !next_statement!(interp) :
           command == "nc" ? !next_call!(interp) : 
           !step_expr(interp)
            if isnull(interp.parent)
                LineEdit.transition(s, :abort)
            else
                oldinterp = interp
                interp = get(oldinterp.parent)
                evaluated!(interp, oldinterp.retval)
            end
        end
        curind = interp.next_expr[1][1]
        range = max(1,curind-2):curind+3
        #print_shadowtree(interp.shadowtree, interp.next_expr[1], range)
        print_status(interp, interp.next_expr[1])
        println()
        return true
    end

    b = Dict{Any,Any}[LineEdit.default_keymap, LineEdit.escape_defaults]
    panel.keymap_dict = LineEdit.keymap(b)

    #print_shadowtree(interp.shadowtree, interp.next_expr[1])
    print_status(interp, interp.next_expr[1])
    Base.REPL.run_interface(repl.t, LineEdit.ModalInterface([panel]))
end

"""
Single step the current function to exit, optionally printing the tree at every
step.

Returns the return value of the interpreted function.
"""
function finish!(interp::Interpreter; print_step::Bool = false, recursive = false)
    while true
        if recursive
            expr = interp.next_expr[2]
            if isa(expr, Expr)
                if expr.head == :call
                    newinterp = enter_call_expr(interp, expr)
                    if newinterp !== nothing
                        finish!(newinterp; print_step = print_step, recursive = true)
                        evaluated!(interp, newinterp.retval)
                        print_step && print_shadowtree(interp.shadowtree, interp.next_expr[1])
                        continue
                    end
                end
            end
        end
        if !step_expr(interp)
            break
        end
        print_step && print_shadowtree(interp.shadowtree, interp.next_expr[1])
    end
    interp.retval
end

macro enter(arg)
    @assert isa(arg, Expr) && arg.head == :call
    quote
        theargs = $(esc(Expr(:tuple,arg.args...)))
        ASTInterpreter.RunDebugREPL(
            ASTInterpreter.enter_call_expr(nothing,Expr(:call,theargs...)))
    end
end

end
