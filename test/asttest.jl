eval(Base,:(have_color = true))
include(Pkg.dir("Gallium","src","astinterpreter.jl"))

#foo() = 1+1
function foo(n)
    x = n+1
    ((BigInt[1 1; 1 0])^x)[2,1]
end


enter(func, env = Environment(Dict(:n => 20),Dict{Symbol,Any}())) = enter(first(methods(func)), env)
function enter(meth::Method, env = Environment(Dict(:n => 20),Dict{Symbol,Any}()))
    ast = Base.uncompressed_ast(meth.func.code)
    tree = ast.args[3]
    AbstractTrees.print_tree(STDOUT, ast.args[3])

    resulttree = copy(tree)
    annotations = AbstractTrees.make_annotations(resulttree) do node
        unevaluated = isa(node, Expr) || isa(node, GlobalRef) || isa(node, Symbol)
        !unevaluated
    end
    shadowtree = AbstractTrees.ShadowTree(Tree(resulttree), Tree(annotations))

    print_tree(STDOUT, resulttree) do io, node
        print(io, typeof(node))
    end

    print_shadowtree(shadowtree)
    it = filter(x->!isa(x[2],LineNumberNode),indenumerate(PostOrderDFS(resulttree)))
    interp = Interpreter(env, tree, it, start(it), nothing, shadowtree, nothing)
    next_expr!(interp)
    print_shadowtree(shadowtree, interp.next_expr[1])
    interp
end

function print_shadowtree(shadowtree, highlight = nothing)
    AbstractTrees.print_tree(STDOUT, shadowtree, withinds = true) do io, annotatednode, inds
        node, evaluated = annotatednode.tree.x, annotatednode.shadow.x.val
        str, _ = pretty_repr(node)
        print_with_color((inds == highlight) ? :yellow : (evaluated ? :green : :red), io, str)
    end
end

#=
for (ind, node) in 

end
=#

import Base: LineEdit, REPL

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

function step_expr(interp)
    ind, node = interp.next_expr

    if isa(node, Expr) && node.head == :return
        interp.retval = node.args[1]
        println("Returning $(node.args[1])")
        return false
    end
    @show ind
    if isa(node, Symbol)
        # Check if we're the LHS of an assignment
        if interp.shadowtree.tree[ind[1:end-1]].head == :(=)
            ret = node
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
            interp.env.locals[lhs] = rhs
            ret = rhs
        elseif node.head == :gotoifnot
            ret = node
            if !node.args[1]
                lind = find_label_index(interp.ast, node.args[2])
                @show lind
                # next_expr! below will move past the label node
                interp.cur_state = next(interp.it,(false,nothing,[lind]))[2]
            end
        else
            ret = eval(node)
        end
    else
        ret = eval(node)
    end
    evaluated!(interp, ret)
end

function evaluated!(interp, ret)
    ind, node = interp.next_expr
    interp.shadowtree[ind] = (ret, AnnotationNode{Any}(true,AnnotationNode{Any}[]))
    ind, node = next_expr!(interp)
    # Skip evaluated values (e.g. constants)
    while interp.shadowtree.shadow[ind].val
        ind, node = next_expr!(interp)
    end
    @show interp.next_expr
    print_shadowtree(interp.shadowtree, interp.next_expr[1])
    return true
end

function to_function(x)
    if isa(x, Function)
        return x
    elseif isa(x, TopNode)
        return Base.(x.name)
    else
        error("Unrecognized")
    end
end

function RunDebugREPL(interp)
    prompt = "debug > "

    repl = Base.active_repl

    # Setup cxx panel
    panel = LineEdit.Prompt(prompt;
        prompt_prefix="\e[38;5;166m",
        prompt_suffix=Base.text_colors[:white],
        on_enter = s->true)

    panel.on_done = (s,buf,ok)->begin
        line = takebuf_string(buf)
        if !ok || strip(line) == "q"
            LineEdit.transition(s, :abort)
        end
        if strip(line) == "s"
            expr = interp.next_expr[2]
            if isa(expr, Expr)
                if expr.head == :call
                    f = to_function(expr.args[1])
                    if isgeneric(f)
                        argtypes = Tuple{map(typeof,expr.args[2:end])...}
                        method = which(f, argtypes)
                        # Construct the environment from the arguments
                        argnames = Base.uncompressed_ast(method.func.code).args[1]
                        env = Dict{Symbol,Any}()
                        for (i,(k,v)) in enumerate(zip(argnames, expr.args[2:end]))
                            # Vararg tuple
                            dump(k)
                            if isa(k, Expr) 
                                if k.head == :(::) && k.args[2].head == :(...)
                                    k = k.args[1]
                                elseif k.head == :(...)
                                    k = k.args[1]
                                else
                                    error()
                                end
                                env[k] = tuple(expr.args[i:end]...)
                                break
                            end
                            env[k] = v
                        end
                        # Add static parameters to invironment
                        (ti, lenv) = ccall(:jl_match_method, Any, (Any, Any, Any),
                             argtypes, method.sig, method.tvars)::SimpleVector
                        @show (ti,lenv)
                        sparams = Dict{Symbol, Any}()
                        i = 1
                        while i < length(lenv)
                            sparams[lenv[i].name] = lenv[i+1]
                            i += 2
                        end
                        newinterp = enter(method,Environment(env,sparams))
                        RunDebugREPL(newinterp)
                        evaluated!(interp, newinterp.retval)
                        return true
                    end
                end
            end
        end
        if !step_expr(interp)
            LineEdit.transition(s, :abort)
        end
        println()
        return true
    end

    b = Dict{Any,Any}[LineEdit.default_keymap, LineEdit.escape_defaults]
    panel.keymap_dict = LineEdit.keymap(b)

    Base.REPL.run_interface(repl.t, LineEdit.ModalInterface([panel]))
end
#RunDebugREPL(enter(foo))

using Hooking
bigfib(x) = ((BigInt[1 1; 1 0])^x)[2,1]

Hooking.hook(bigfib,Tuple{Int}) do hook, RC
    RunDebugREPL(enter(bigfib, Environment(Dict(:x => 20),Dict{Symbol,Any}())))
end
