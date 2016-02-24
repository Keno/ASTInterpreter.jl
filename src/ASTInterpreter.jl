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
    annotations = AbstractTrees.make_annotations(resulttree, resulttree, false) do node, parent, parent_ev
        if parent_ev
            return parent_ev
        end
        unevaluated = isa(node, Expr) || isa(node, GlobalRef) || isa(node, Symbol) ||
            isa(node,GenSym) || isa(node, GotoNode) || isa(node, QuoteNode)
        if isa(node, Expr) && (node.head == :meta || node.head == :boundscheck ||
            node.head == :inbounds)
            unevaluated = false
        end
        if (isa(node, GenSym) || isa(node, Symbol)) && isexpr(parent,:(=)) && parent.args[1] == node
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
    ast = Base.uncompressed_ast(meth.func.def)
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

abstract ReplacementLoc

immutable SimpleReplacementLoc <: ReplacementLoc
    replacing::SourceRange
    before::AbstractString
    after::AbstractString
end
Lexer.normalize(x::ReplacementLoc) = x.replacing
Lexer.merge(x::ReplacementLoc,y::ReplacementLoc) =
    Lexer.merge(Lexer.normalize(x),Lexer.normalize(y))
Lexer.merge(x,y::ReplacementLoc) = Lexer.merge(x,Lexer.normalize(y))
Lexer.merge(x::ReplacementLoc,y) = Lexer.merge(Lexer.normalize(x),y)

# SequencingReplacementLoc
type SRLoc <: ReplacementLoc
    replacing::SourceRange
    sequence::Vector{Any}
    lastidx::Int
end

function sequence!(s::SRLoc, ind)
    sidx = findnext(x->x==0,s.sequence,s.lastidx+1)
    s.sequence[sidx] = ind
    s.lastidx = sidx
    s
end

immutable Coloring
    x
    color::Symbol
end
Base.print(io::IO, c::Coloring) = print_with_color(c.color, string(c.x))
Base.show_unquoted(io::IO, c::Coloring, x, y) =
    print_with_color(c.color, sprint(Base.show_unquoted, c.x, x, y))

function annotate_highlights!(x, highlights)
    wrapcolor = nothing
    for highlight in highlights
        if isempty(highlight[1])
            wrapcolor = highlight[2]
        else
            Tree(x)[highlight[1]] = Coloring(Tree(x)[highlight[1]], highlight[2])
        end
    end
    wrapcolor == nothing ? x : Coloring(x, wrapcolor)
end

function print_status(interp, highlight = nothing)
    if interp.loctree === nothing
        print_shadowtree(interp.shadowtree, highlight)
    else
        union = Lexer.normalize(reduce(⤄,PostOrderDFS(interp.loctree)))
        file = SourceFile(interp.code)
        startline = compute_line(file, union.offset)
        stopline = compute_line(file, union.offset+union.length)
        if highlight != nothing
            x = AbstractTrees.getindexhighest(Tree(interp.loctree),highlight)
            highlighstart = x[1]
            while Lexer.normalize(Tree(interp.loctree)[highlighstart]) == SourceRange()
                highlighstart = highlighstart[1:(end-1)]
                !isempty(highlighstart) || break
            end
            locnode = Tree(interp.loctree)[highlighstart]
            offset = Lexer.normalize(locnode).offset

            if offset != -1 % UInt32
                offsetline = compute_line(file, offset)
                startoffset = max(file.offsets[max(offsetline-3,1)], file.offsets[startline])
                stopoffset = endof(interp.code)-1
                if offsetline + 3 < endof(file.offsets)
                    stopoffset = min(stopoffset, file.offsets[offsetline + 3]-1)
                end
                if stopline + 1 < endof(file.offsets)
                    stopoffset = min(stopoffset, file.offsets[stopline + 1]-1)
                end

                ###### New Algorithm
                idxstartwiwth(idxs, start) = length(idxs) >= length(start) && idxs[1:length(start)] == start
                ishighlight(x) = idxstartwiwth(x,highlight)
                
                # Figure out all indices we want to print
                indices = Set{Vector{Int}}()
                srlocs = Set{SRLoc}()
                locs = Vector{Any}()
                highlighting = Vector{Any}()
                for (ind, isevaluated) in indenumerate(PostOrderDFS(interp.shadowtree.shadow))
                    if (ishighlight(ind) && length(ind)==length(highlight)) ||
                       (!ishighlight(ind) && isevaluated.val)
                        orgind = copy(ind)
                        while !isempty(ind) && try
                                Lexer.normalize(Tree(interp.loctree)[ind])
                            catch e
                                isa(e, BoundsError) || rethrow(e)
                                SourceRange()
                            end == SourceRange()
                            ind = ind[1:end-1]
                        end
                        locnode = Tree(interp.loctree)[ind]
                        if Lexer.normalize(locnode) == SourceRange() || ind == []
                            continue
                        end
                        off = Lexer.normalize(locnode).offset
                        if off > stopoffset || off < startoffset
                            continue
                        end
                        push!(highlighting,(ind, orgind, ishighlight(orgind) ? :yellow : :green))
                        if isa(locnode.loc, SRLoc)
                            if !ishighlight(orgind)
                                continue
                            end
                            r = locnode.loc
                            r in srlocs && continue
                            push!(srlocs, r)
                        else
                            r = ind
                            r in indices && continue
                            push!(indices, r)
                        end
                        push!(locs,(Lexer.normalize(locnode),r))
                    end
                end
                
                # Collect indices that the srlocs care about as well
                for srloc in srlocs
                    for e in srloc.sequence
                        if isa(e,Array)
                            push!(indices, e)
                        end
                    end
                end
                
                # Turn indices into an array. We will use indices into this
                # array to associate them with the highlight information below
                indices = sort(collect(indices), lt = lexless)
                
                # Remove any indices whose prefix is on the list
                prev = [-1]
                newinds = Any[]
                for ind in indices
                    if !idxstartwiwth(ind, prev)
                        push!(newinds, ind)
                        prev = ind
                    end
                end
                indices = newinds
                
                ## Now go back and record highlight information
                highlighinfo = Any[Any[] for _ in 1:length(indices)]
                for x in highlighting
                    ind = x[1]
                    while true
                        r = searchsorted(indices, ind, lt = lexless)
                        if length(r) != 0
                            push!(highlighinfo[first(r)],(x[2][(length(ind)+1):end],x[3]))
                            break
                        end
                        if ind == []
                            break
                        end
                        ind = ind[1:end-1]
                    end
                end
                
                sort!(locs, by = x->Lexer.normalize(x[1]).offset)
                append!(locs,map(
                    Lexer.sortedcomplement(SourceRange(startoffset,stopoffset-startoffset+1,0),
                    filter(x->Lexer.normalize(x).offset >= startoffset, map(x->x[1],locs)))) do x
                    off = x.offset
                    code = interp.code[off+1:(off+x.length)]
                    x, code
                end)
                sort!(locs, by = x->Lexer.normalize(x[1]).offset)
                
                # Compute necessary data for line numbering
                startline = compute_line(file, startoffset)
                stopline = compute_line(file, stopoffset)
                current_line = startline
                stoplinelength = length(string(stopline))
                
                print(startline, " "^(stoplinelength-length(string(startline))+1))
                
                function print_piece(piece, implicit = true)
                    if isa(piece,Array)
                        r = searchsorted(indices, piece, lt = lexless)
                        val = Tree(interp.shadowtree.tree)[piece]
                        if length(r) == 0
                            return
                        end
                        highlights = highlighinfo[first(r)]
                        print(annotate_highlights!(deepcopy(val), highlights))
                    elseif isa(piece,Coloring)
                        print(piece)
                    else
                        lines = split(piece, '\n', keep = true)
                        print_with_color(:white, lines[1])
                        for line in lines[2:end]
                            if !implicit
                                current_line += 1
                                lineno = string(current_line)
                            else
                                lineno = string('↳')
                            end
                            print('\n',lineno, " "^(stoplinelength-length(lineno)+1),line)
                        end
                    end
                end
                
                
                for loc in locs
                    if isa(loc[2],SRLoc)
                        for x in loc[2].sequence
                            print_piece(x, true)
                        end
                    else
                        print_piece(loc[2], false)
                    end
                end
                
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
            # Special case hack for readability.
            # ret = rhs
            ret = node
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
                ret = f(node.args[2:end]...)
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

#TODO: The method should probably just start at it's first definition line
function is_function_def(ex)
    (isa(ex,Expr) && ex.head == :(=) && isexpr(ex.args[1],:call)) ||
    isexpr(ex,:function)
end

function collectcalls(file, parsedexpr, parsedloc)
    thecalls = Any[]
    theassignments = Any[]
    forlocs = Any[]
    active_fors = Any[]
    for (ind,node) in indenumerate(PostOrderDFS(parsedexpr))
        parent = Tree(parsedexpr)[ind[1:end-1]]
        if isexpr(node, :call) || isa(node, Tuple)
            push!(thecalls, (Tree(parsedloc)[ind],node))
        end
        # If our parent is a for and we're the first child, insert, the entry
        # iteration lowering now.
        if isexpr(parent, :for) && ind[end] == 1
            forrange = Lexer.normalize(Tree(parsedloc)[ind[1:end-1]])
            argrange = Lexer.normalize(Tree(parsedloc)[ind])
            active_reprange = SourceRange(forrange.offset,argrange.offset+argrange.length-forrange.offset,0)
            l = compute_line(file,active_reprange.offset)
            padding = (active_reprange.offset - file.offsets[l])+1
            # Lowering for x in y
            loc = SRLoc(active_reprange,
                [0, # A = y
                string("\n"," "^padding),
                0, # B = start(A)
                string("\n"," "^padding,"while "),
                0,  # !done(A,B)
                string("\n"," "^(padding+4)),
                0,  # C = next(A,B)
                string("\n"," "^(padding+4)),
                0,  # x = C.1
                string("\n"," "^(padding+4)),
                0], # B = C.2
                0
            )
            
            push!(active_fors,(loc,active_reprange))
            
            push!(thecalls,(SourceRange(),nothing))         # Start
            push!(thecalls,(SourceRange(),nothing))         # done
            push!(thecalls,(loc,          nothing))         # !
            push!(thecalls,(SourceRange(),nothing))         # next
            push!(thecalls,(SourceRange(), nothing))        # getfield
            push!(thecalls,(SourceRange(), nothing))        # getfield
            
            push!(theassignments, (loc, nothing))                  # A = y
            push!(theassignments, (loc, nothing))                  # B = start(A)
            push!(theassignments, (loc, nothing))                  # gensym() = next()
            push!(theassignments, (loc, nothing))        # gensym() = ans.1
            push!(theassignments, (loc, nothing))        # gensym() = ans.2
        elseif isexpr(node, :(=))
            push!(theassignments, (Tree(parsedloc)[ind],node))
        end
        
        # Now that we've processed the body, insert the end-of-body iteration
        # stuff
        if isexpr(node, :for)
            active_forloc, active_reprange = pop!(active_fors)
            loc2 = SRLoc(active_reprange,[0;],0)
            push!(thecalls, (SourceRange(),nothing))               # done
            push!(thecalls, (SourceRange(),nothing))               # !
            push!(thecalls, (loc2,nothing))                        # !
            push!(forlocs, (active_forloc, loc2))
            active_forloc = nothing
        end
    end
    thecalls = thecalls[2:end], theassignments, forlocs
end

function expression_mismatch(loweredast, thecalls, theassignments, forlocs)
    println("Failed to match parsed and lowered ASTs. This is a bug (or rather missing coverage).")
    println("Falling back to unsugared mode.")
    println("I attempted the following matching:")
    loctree = treemap(PostOrderDFS(loweredast)) do ind, node, childlocs
        if isexpr(node, :call)
            isempty(thecalls) && return nothing
            candidate = shift!(thecalls)
            println("Matching call $node with $candidate")
        elseif isexpr(node, :(=))
            isempty(theassignments) && return nothing
            println("Matching assignment $node with $(shift!(theassignments))")
        end
        nothing
    end
end

immutable MatchingError
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
    if !is_function_def(res.expr)
        # Retry parsing the line before
        seekstart(buf)
        for _ in (line-1):-1:2
            readuntil(buf,'\n')
        end
        ts = Lexer.TokenStream{Lexer.SourceLocToken}(buf)
        res = Parser.parse(ts)
    end
    lower!(res)
    parsedexpr = res.expr
    parsedloc = res.loc
    loweredast = Base.uncompressed_ast(meth.func.code).args[3]
    thecalls, theassignments, forlocs = collectcalls(SourceFile(contents), parsedexpr, parsedloc)
    loctree = try
        treemap(PostOrderDFS(loweredast)) do ind, node, childlocs
            if isexpr(node, :call)
                call = node.args[1]
                isempty(thecalls) && throw(MatchingError())
                candidate = shift!(thecalls)
                if isa(candidate[1], SRLoc)
                    ASTInterpreter.sequence!(candidate[1], ind)
                    SourceNode(candidate[1],childlocs)
                else
                    candidate[1]
                end
            elseif isexpr(node, :(=))
                isempty(theassignments) && throw(MatchingError())
                x = shift!(theassignments)
                x = x[1]
                if isa(x, SRLoc)
                    ASTInterpreter.sequence!(x, ind)
                    SourceNode(x,childlocs)
                else
                    x
                end
            else
                SourceNode(SourceRange(),childlocs)
            end
        end
    catch err
        isa(err, MatchingError) || rethrow(err)
        expression_mismatch(loweredast, collectcalls(SourceFile(contents), parsedexpr, parsedloc)...)
        nothing
    end

    function postprocess!(loctree, forlocs)
        for (forloc,forloc2) in forlocs
            # Add a location to the parent of !done
            negind = forloc.sequence[5][1:(end-1)]
            newloc1 = deepcopy(forloc)
            newloc2 = deepcopy(forloc)
            # TODO: This really needs to have a better way
            newloc1.sequence[4] = ASTInterpreter.Coloring(newloc1.sequence[4],:yellow)
            Tree(loctree)[negind] = SourceNode(newloc1,Tree(loctree)[negind].children)
            # Next Hack
            rind = forloc2.sequence[1]
            negrind = rind[1:(end-1)]
            newloc2.sequence[4] = string(forloc.sequence[4],"!")
            newloc2.sequence[5] = rind
            newloc3 = deepcopy(newloc2)
            newloc3.sequence[4] = ASTInterpreter.Coloring(newloc3.sequence[4],:yellow)
            Tree(loctree)[rind] = SourceNode(newloc2,Tree(loctree)[rind].children)
            Tree(loctree)[negrind] = SourceNode(newloc3,Tree(loctree)[negrind].children)
        end
    end
    if loctree != nothing
        postprocess!(loctree, forlocs)
        # Make sure we have the whole bounds of the function
        loctree = SourceNode(Lexer.normalize(reduce(⤄,PostOrderDFS(parsedloc))),loctree.children)
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

    # Skip evaluated values (e.g. constants)
    ind, node = interp.next_expr[1]
    while interp.shadowtree.shadow[ind].val
        ind, node = next_expr!(interp)
    end

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

include("lowering.jl")

end
