module ASTInterpreter

export enter, Environment, @enter
import Base: LineEdit, REPL

using AbstractTrees
using JuliaParser
using JuliaParser.Lexer
using Base.Meta
import JuliaParser.Lexer: SourceNode, SourceRange
import JuliaParser.Parser: diag

import AbstractTrees: children, printnode

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
    locals::Vector{Nullable{Any}}
    gensyms::Vector{Any}
    sparams::Vector{Any}
end

Base.copy(e::Environment) = Environment(copy(e.locals), copy(e.gensyms), copy(e.sparams))

type Interpreter
    stack::Vector{Any}
    env::Environment
    linfo::LambdaInfo
    ast::Any
    it::Any
    cur_state::Any
    next_expr::Any
    shadowtree::Any
    code::AbstractString
    loctree::Any
    retval::Any
    exception_frames::Vector{Int}
end

function make_shadowtree(tree)
    resulttree = copy(tree)
    annotations = AbstractTrees.make_annotations(resulttree, resulttree, false) do node, parent, parent_ev
        if parent_ev
            return parent_ev
        end
        unevaluated = isa(node, Expr) || isa(node, GlobalRef) || isa(node, Symbol) || isa(node,Slot) ||
            isa(node,GenSym) || isa(node, GotoNode) || isa(node, QuoteNode) || isa(node, TopNode)
        if isa(node, Expr) && (node.head == :meta || node.head == :boundscheck ||
            node.head == :inbounds || node.head == :line)
            unevaluated = false
        end
        if (isa(node, GenSym) || isa(node, Symbol) || isa(node, Slot) || isa(node,GlobalRef)) && isexpr(parent,:(=)) && parent.args[1] == node
            unevaluated = false
        end
        if isexpr(parent, :static_typeof)
            unevaluated = false
        end
        !unevaluated
    end
    shadowtree = AbstractTrees.ShadowTree(Tree(resulttree), Tree(annotations))
    it = filter(x->true,indenumerate(PostOrderDFS(resulttree)))
    shadowtree, it
end

function enter(linfo, tree::Expr, env, stack = Any[]; loctree = nothing, code = "")
    shadowtree, it = make_shadowtree(tree)

    interp = Interpreter(stack, env, linfo, tree, it,
        start(it), nothing, shadowtree, code, loctree, nothing, Vector{Int}())
    push!(stack, interp)
    ind, node = next_expr!(interp)

    while interp.shadowtree.shadow[ind].val
        ind, node = next_expr!(interp)
    end

    interp
end
function enter(meth::Method, env::Environment, stack = Any[]; kwargs...)
    linfo = meth.func
    code = Base.uncompressed_ast(linfo.def)
    tree = Expr(:body); tree.args = code
    enter(linfo, tree, env, stack; kwargs...)
end
function enter(linfo::LambdaInfo, env::Environment, stack = Any[]; kwargs...)
    if linfo.inferred
        f = (linfo.module).(linfo.name)
        meth = which(f,Tuple{linfo.specTypes.parameters[2:end]...})
        return enter(meth, env, stack; kwargs...)
    end
    code = Base.uncompressed_ast(linfo)
    tree = Expr(:body); tree.args = code
    enter(linfo, tree, env, stack; kwargs...)
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
Lexer.merge(x::ReplacementLoc,y::Void) = Lexer.merge(Lexer.normalize(x),y)
Lexer.merge(x::ReplacementLoc,y::Lexer.Token) = Lexer.merge(Lexer.normalize(x),y)
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

function determine_line(interp, highlight)
    line = interp.linfo.line
    # Find a line number node previous to this expression
    if highlight !== nothing
        exprtree = interp.shadowtree.tree.x
        for i = highlight[1]:-1:1
            expr = exprtree.args[i]
            if isa(expr, LineNumberNode)
                line = expr.line
                break
            elseif isexpr(expr, :line)
                line = expr.args[1]
                break
            end
        end
    end
    line
end

function print_sourcecode(linfo, code, line; file = SourceFile(code))
    startoffset, stopoffset = compute_source_offsets(code, file.offsets[line],
        linfo.line-1, line+3; file=file)

    # Compute necessary data for line numbering
    startline = compute_line(file, startoffset)
    stopline = compute_line(file, stopoffset)
    current_line = line
    stoplinelength = length(string(stopline))

    code = split(code[(startoffset:stopoffset)+1],'\n')
    lineno = startline

    if !isempty(code) && isempty(code[end])
        pop!(code)
    end

    for textline in code
        print_with_color(lineno == current_line ? :yellow : :white,
            string(lineno, " "^(stoplinelength-length(lineno)+1)))
        println(textline)
        lineno += 1
    end
    println()
end

"""
Determine the offsets in the source code to print, based on the offset of the
currently highlighted part of the code, and the start and stop line of the
entire function.
"""
function compute_source_offsets(code, offset, startline, stopline; file = SourceFile(interp.code))
    offsetline = compute_line(file, offset)
    startoffset = max(file.offsets[max(offsetline-3,1)], file.offsets[startline])
    stopoffset = endof(code)-1
    if offsetline + 3 < endof(file.offsets)
        stopoffset = min(stopoffset, file.offsets[offsetline + 3]-1)
    end
    if stopline + 1 < endof(file.offsets)
        stopoffset = min(stopoffset, file.offsets[stopline + 1]-1)
    end
    startoffset, stopoffset
end

global fancy_mode = false

function print_status(interp, highlight = interp.next_expr[1]; fancy = fancy_mode)
    if !fancy && !isempty(interp.code)
        print_sourcecode(interp.linfo, interp.code, determine_line(interp, highlight))
        ex = interp.shadowtree[highlight].tree.x
        # print slots with their names
        wrap = !isa(ex,Expr)
        ex = wrap ? Expr(:block, ex) : copy(ex)
        treemap!(function (x)
                     if isa(x, Slot)
                         name = interp.linfo.slotnames[x.id]
                         return sym_visible(name) ? name : x
                     else
                         return x
                     end
                 end,
                 PreOrderDFS(ex))
        if wrap; ex = ex.args[1]; end
        println("About to run: ", ex)
    elseif interp.loctree === nothing
        print_shadowtree(interp.shadowtree, highlight)
    else
        union = Lexer.normalize(reduce(⤄,PostOrderDFS(interp.loctree)))
        file = SourceFile(interp.code)
        # Compute the start and stop line of the current function
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
                startoffset, stopoffset =
                    compute_source_offsets(interp.code, offset, startline,
                        stopline, file = file)

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
    next_expr!(interp)
    return done!(interp)
end

const fancy_backtraces = true

function _step_expr(interp)
    ind, node = interp.next_expr
    local ret
    try
        if isa(node, Expr) && node.head == :return
            interp.retval = node.args[1]
            return false
        end
        if isa(node, Slot) || isa(node,GenSym)
            # Check if we're the LHS of an assignment
            if ind[end] == 1 && interp.shadowtree.tree[ind[1:end-1]].head == :(=)
                ret = node
            elseif isa(node,GenSym)
                ret = interp.env.gensyms[node.id+1]
            else
                nslots = length(interp.env.locals)
                id = node.id
                if id > nslots
                    # hack: static parameters placed at end of locals for interactive exprs
                    ret = interp.env.sparams[id - nslots]
                else
                    val = interp.env.locals[id]
                    if isnull(val)
                        sym = interp.linfo.slotnames[id]
                        error("local variable $sym not defined")
                    end
                    ret = get(val)
                end
            end
        elseif isa(node, Expr)
            if node.head == :(=)
                lhs = node.args[1]
                rhs = node.args[2]
                if isa(lhs, GenSym)
                    interp.env.gensyms[lhs.id+1] = rhs
                elseif isa(lhs, Slot)
                    interp.env.locals[lhs.id] = Nullable{Any}(rhs)
                elseif isa(lhs, GlobalRef)
                    eval(:($lhs = $(QuoteNode(rhs))))
                end
                # Special case hack for readability.
                # ret = rhs
                ret = node
            elseif node.head == :&
                ret = node
            elseif node.head == :gotoifnot
                ret = node
                if !isa(node.args[1], Bool)
                    throw(TypeError(interp.linfo.name, "if", Bool, node.args[1]))
                end
                if !node.args[1]
                    return goto!(interp, node.args[2])
                end
            elseif node.head == :call
                # Don't go through eval since this may have unqouted, symbols and
                # exprs
                f = to_function(node.args[1])
                if isa(f, Core.IntrinsicFunction)
                    # Special handling to quote any literal symbols that may still
                    # be in here, so we can pass it into eval
                    for i in 1:length(node.args)
                        if isa(node.args[i], Union{Symbol,GenSym,Slot,GlobalRef})
                            node.args[i] = QuoteNode(node.args[i])
                        end
                    end
                    ret = eval(node)
                else
                    # Don't go through eval since this may have unqouted, symbols and
                    # exprs
                    ret = f(node.args[2:end]...)
                end
            elseif node.head == :static_typeof
                ret = Any
            elseif node.head == :type_goto
                ret = nothing
            elseif node.head == :enter
                push!(interp.exception_frames, node.args[1])
                ret = node
            elseif node.head == :leave
                for _ = 1:node.args[1]
                    pop!(interp.exception_frames)
                end
                ret = node
            elseif node.head == :static_parameter
                ret = interp.env.sparams[node.args[1]]
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
    catch err
        (!fancy_backtraces || interp.loctree == nothing) && rethrow(err)
        buf = IOBuffer()
        Base.showerror(buf, err)
        D = diag(SourceRange(),takebuf_string(buf))
        diag(D, Tree(interp.loctree)[ind].loc, "while running this expression", :note)
        rethrow(D)
    end
    _evaluated!(interp, ret)
    true
end
step_expr(interp) = (r = _step_expr(interp); done!(interp); r)

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

function next_until!(f,interp)
    ind, node = interp.next_expr
    while step_expr(interp)
        ind, node = interp.next_expr
        f(node) && return true
    end
    return false
end
next_call!(interp) = next_until!(node->isexpr(node,:call)||isexpr(node,:return), interp)

function changed_line(expr, line)
    if isa(expr, LineNumberNode)
        return expr.line != line
    elseif isa(expr, Expr) && isexpr(expr, :line)
        return expr.args[1] != line
    else
        return false
    end
end

isgotonode(node) = isa(node, GotoNode) || isexpr(node, :gotoifnot)

function next_line!(interp)
    didchangeline = false
    line = determine_line(interp, interp.next_expr[1])
    first = true
    while !didchangeline
        ind, node = interp.next_expr
        # Skip evaluated values (e.g. constants)
        while interp.shadowtree.shadow[ind].val
            didchangeline = changed_line(node, line)
            didchangeline && break
            ind, node = next_expr!(interp)
        end
        didchangeline && break
        ind, node = interp.next_expr
        # If this is a return node, interrupt execution. This is the same
        # special case as in `s`.
        (!first && isexpr(node, :return)) && return true
        first = false
        # If this is a goto node, step it and reevaluate
        if isgotonode(node)
            _step_expr(interp) || return false
            didchangeline = line != determine_line(interp, interp.next_expr[1])
        else
            _step_expr(interp) || return false
        end
    end
    done!(interp)
    # Ok, we stepped to the next line. Now step through to the next call
    call_or_assignment(node) = isexpr(node,:call) || isexpr(node,:(=)) || isexpr(node, :return)
    call_or_assignment(interp.next_expr[2]) ||
        next_until!(call_or_assignment, interp)
end

function _evaluated!(interp, ret)
    ind, node = interp.next_expr
    interp.shadowtree[ind] = (ret, AnnotationNode{Any}(true,AnnotationNode{Any}[]))
end
evaluated!(interp, ret) = (_evaluated!(interp, ret); done!(interp))

"""
Advance to the next evaluatable statement
"""
function done!(interp)
    ind, node = interp.next_expr
    # Skip evaluated values (e.g. constants)
    while interp.shadowtree.shadow[ind].val
        ind, node = next_expr!(interp)
    end
    return true
end

function to_function(x)
    if isa(x, Function) || isa(x, Core.IntrinsicFunction)
        x
    elseif isa(x, TopNode)
        Base.(x.name)
    elseif isa(x, GlobalRef)
        eval(x)
    else
        x
    end
end

_Typeof(x) = isa(x,Type) ? Type{x} : typeof(x)

#TODO: The method should probably just start at it's first definition line
function is_function_def(ex)
    (isa(ex,Expr) && ex.head == :(=) && isexpr(ex.args[1],:call)) ||
    isexpr(ex,:function)
end

function collectcalls(file, parsedexpr, parsedloc, complete = true)
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
        elseif isexpr(node, :(&&))
            push!(theassignments, (SourceRange(), nothing))
            push!(theassignments, (SourceRange(), nothing))
        end
    end
    thecalls = complete ? thecalls[2:end] : thecalls, theassignments, forlocs
end

function expression_mismatch(loweredast, parsedexpr, thecalls, theassignments, forlocs)
    if !fancy_mode
        return nothing
    end
    println("Failed to match parsed and lowered ASTs. This is a bug (or rather missing coverage).")
    println("Falling back to unsugared mode.")
    println("I attempted the following matching:")
    display(Tree(loweredast))
    display(Tree(parsedexpr))
    treemap(PostOrderDFS(loweredast)) do ind, node, childlocs
        if isexpr(node, :call)
            if isempty(thecalls)
                println("Failed to match $node")
                return
            end
            candidate = shift!(thecalls)
            println("Matching call $node with $candidate")
        elseif isexpr(node, :(=))
            if isempty(theassignments)
                println("Failed to match $node")
                return    
            end
            println("Matching assignment $node with $(shift!(theassignments))")
        end
        nothing
    end
end

immutable MatchingError
end

function process_loctree(res, contents, linfo, complete = true)
    lower!(res)
    parsedexpr = Lexer.¬(res)
    parsedloc = Lexer.√(res)
    stmts = Base.uncompressed_ast(linfo)
    loweredast = Expr(:body); loweredast.args = stmts
    local thecalls, theassignments, forlocs
    loctree = try
        thecalls, theassignments, forlocs = collectcalls(SourceFile(contents), parsedexpr, parsedloc, complete)
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
        if isa(err, MatchingError) 
            expression_mismatch(loweredast, parsedexpr, collectcalls(SourceFile(contents), parsedexpr, parsedloc, complete)...)
        elseif fancy_mode
            rethrow(err)
        end
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
        end
    end
    if loctree != nothing
        postprocess!(loctree, forlocs)
        # Make sure we have the whole bounds of the function
        loctree = SourceNode(Lexer.normalize(reduce(⤄,PostOrderDFS(parsedloc))),loctree.children)
    end

    loctree, contents    
end

function reparse_meth(meth)
    if isa(meth, LambdaInfo)
        linfo = meth.def.def
        file, line = Base.find_source_file(string(linfo.file)), linfo.line
    else
        linfo = meth.func.def
        file, line = functionloc(meth)
    end
    if file === nothing
        return nothing, ""
    end
    contents = open(readstring, file)
    buf = IOBuffer(contents)
    for _ in line:-1:2
        readuntil(buf,'\n')
    end
    ts = Lexer.TokenStream{Lexer.SourceLocToken}(buf)
    local res, ts
    try
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
    catch err
        if !fancy_mode
            return nothing, contents
        end
        rethrow(err)
    end
    process_loctree(res, contents, linfo)
end

function prepare_locals(linfo, argvals = ())
    # Construct the environment from the arguments
    argnames = linfo.slotnames[1:linfo.nargs]
    locals = Array(Nullable{Any}, length(linfo.slotflags))
    ng = isa(linfo.gensymtypes, Int) ? linfo.gensymtypes : length(linfo.gensymtypes)
    gensyms = Array(Any, ng)
    sparams = Array(Any, length(linfo.sparam_syms))
    if argvals != () && length(argvals) < length(argnames) # Empty Vararg
        locals[linfo.nargs] = ()
    end
    for i = 1:linfo.nargs
        if linfo.isva && i == length(argnames)
            locals[i] = length(argvals) >= i ? tuple(argvals[i:end]...) : Nullable{Any}()
            break
        end
        locals[i] = length(argvals) >= i ? Nullable{Any}(argvals[i]) : Nullable{Any}()
    end
    # add local variables initially undefined
    for i = (linfo.nargs+1):length(linfo.slotnames)
        locals[i] = Nullable{Any}()
    end
    Environment(locals, gensyms, sparams)
end

function enter_call_expr(interp, expr)
    f = to_function(expr.args[1])
    allargs = expr.args
    if is(f,Base._apply)
        f = to_function(allargs[2])
        if isa(allargs[3],Tuple) && length(allargs) == 3
            allargs = [allargs[2], allargs[3]...]
        else
            allargs = allargs[2:end]
        end
    end
    if !isa(f, Core.Builtin) && !isa(f, Core.IntrinsicFunction)
        args = allargs[2:end]
        argtypes = Tuple{map(_Typeof,args)...}
        method = try
            which(f, argtypes)
        catch err
            println(f)
            println(argtypes)
            rethrow(err)
        end
        argtypes = Tuple{_Typeof(f), argtypes.parameters...}
        args = allargs
        env = prepare_locals(method.func, args)
        # Add static parameters to environment
        (ti, lenv) = ccall(:jl_match_method, Any, (Any, Any, Any),
                           argtypes, method.sig, method.tvars)::SimpleVector
        for i = 1:length(lenv)
            env.sparams[i] = lenv[i]
        end
        loctree, code = reparse_meth(method)
        newinterp = enter(method,env,interp != nothing ? interp.stack : Any[], loctree = loctree, code = code)
        return newinterp
    end
    nothing
end

function print_linfo_desc(io::IO, linfo)
    argnames = linfo.slotnames[2:linfo.nargs]
    spectypes = Any[Any for i=1:length(argnames)] #linfo.slottypes[2:end]
    print(linfo.name,'(')
    first = true
    for (argname, argT) in zip(argnames, spectypes)
        first || print(io, ", ")
        first = false
        print(argname)
        !isa(argT, Any) && print("::", argT)
    end
    println(") at ",linfo.file,":",linfo.line)
end

function sym_visible(name)
    sn = string(name)
    if startswith(sn, "#")
        lasthash = rsearchindex(sn, "#")
        if lasthash == 1  # mangled names have 2 '#'s in them,
            return false  # hidden names have 1.
        end
    end
    if sn == "#temp#" || name == :__temp__
        return false
    end
    return true
end

function print_var(io::IO, name, val::Nullable, undef_callback)
    if sym_visible(name)
        print("  | ")
        if isnull(val)
            print(io, name, " = ")
            undef_callback(io,name)
        else
            val = get(val)
            println(io, name, "::", typeof(val), " = ", val)
        end
    end
end

function print_locals(io::IO, linfo, env::Environment, undef_callback)
    for i = 1:length(env.locals)
        print_var(io, linfo.slotnames[i], env.locals[i], undef_callback)
    end
    for i = 1:length(env.sparams)
        print_var(io, linfo.sparam_syms[i], Nullable{Any}(env.sparams[i]), undef_callback)
    end
end

function print_backtrace(interp)
    num = 1
    for frame in reverse(interp.stack)
        print_frame(STDOUT, num, frame)
        num += 1
    end
end

function print_frame(io::IO, num, interp::Interpreter)
    print(io, "[$num] ")
    print_linfo_desc(io, interp.linfo)
    print_locals(io, interp.linfo, interp.env,
        (io,name)->println(io, "<undefined>"))
end
print_backtrace(_::Void) = nothing

include(joinpath(dirname(@__FILE__),"..","..","JuliaParser","src","interactiveutil.jl"))

get_env_for_eval(interp::Interpreter) = interp.env
get_linfo(interp::Interpreter) = interp.linfo

function unknown_command(interp::Interpreter, command)
    print_with_color(:red,"\nUnknown command!\n");
end

function finish_until!(top_interp, interp)
    while true
        if top_interp == interp
            return interp
        end
        finish!(top_interp)
        oldinterp = pop!(top_interp.stack)
        top_interp = oldinterp.stack[end]
        evaluated!(top_interp, oldinterp.retval)
    end
    interp
end

can_step(_) = false
can_step(interp::Interpreter) = true

loc_if_available(interp, ind) = try
    Tree(interp.loctree)[ind].loc
catch err
    isa(err, BoundsError) || rethrow(err)
    SourceRange()
end

function process_exception!(interp::Interpreter, D::Parser.Diagnostic, istop)
    if !isempty(interp.exception_frames)
        target = interp.exception_frames[end]
        goto!(interp, target)
        ind, _ = interp.next_expr
        diag(D, loc_if_available(interp, ind), "caught here",:note)
        return true
    else
        ind, _ = interp.next_expr
        !istop && diag(D, loc_if_available(interp, ind), "while evaluating expression",:note)
        return false
    end
end

function RunDebugREPL(top_interp)
    level = 1
    prompt(level, name) = "$level|$name > "

    repl = Base.active_repl

    # Setup debug panel
    panel = LineEdit.Prompt(prompt(level, "debug");
        prompt_prefix="\e[38;5;166m",
        prompt_suffix=Base.text_colors[:white],
        on_enter = s->true)

    # For now use the regular REPL completion provider
    replc = Base.REPL.REPLCompletionProvider(repl)

    # Set up the main Julia prompt
    julia_prompt = LineEdit.Prompt(prompt(level, "julia");
        # Copy colors from the prompt object
        prompt_prefix = repl.prompt_color,
        prompt_suffix = (repl.envcolors ? Base.input_color : repl.input_color),
        complete = replc,
        on_enter = Base.REPL.return_callback)

    panel.hist = REPL.REPLHistoryProvider(Dict{Symbol,Any}(:debug => panel,
        :julia => julia_prompt))
    julia_prompt.hist = panel.hist
    Base.REPL.history_reset_state(panel.hist)

    search_prompt, skeymap = Base.LineEdit.setup_search_keymap(panel.hist)
    search_prompt.complete = Base.REPL.LatexCompletions()


    function done_stepping(s, interp; to_next_call = false)
        stack = interp.stack
        this_idx = findfirst(stack, interp)
        if this_idx == 0
            LineEdit.transition(s, :abort)
            interp = nothing
        else
            oldinterp = interp
            interp = this_idx == 1 ? nothing : stack[this_idx-1]
            resize!(stack, this_idx-1)
            if !isa(interp, Interpreter)
                LineEdit.transition(s, :abort)
                return nothing
            end
            evaluated!(interp, oldinterp.retval)
            to_next_call &&
              (isexpr(interp.next_expr[2], :call) || next_call!(interp))
            print_status(interp, interp.next_expr[1])
            println()
        end
        interp
    end

    interp = top_interp

    panel.on_done = (s,buf,ok)->begin
        line = takebuf_string(buf)
        old_level = level
        if !ok || strip(line) == "q"
            LineEdit.transition(s, :abort)
            LineEdit.reset_state(s)
            return false
        end
        if isempty(strip(line)) && length(panel.hist.history) > 0
            command = panel.hist.history[end]
        else
            command = strip(line)
        end
        if command == "si" || command == "s"
            first = true
            while true
                expr = interp.next_expr[2]
                if isa(expr, Expr)
                    if expr.head == :call && !isa(expr.args[1],Core.IntrinsicFunction)
                        x = enter_call_expr(interp, expr)
                        if x !== nothing
                            interp = top_interp = x
                            print_status(interp, interp.next_expr[1])
                            LineEdit.reset_state(s)
                            return true
                        end
                    elseif !first && isexpr(expr, :return)
                        # As a special case, do not step through a return
                        # statement, unless the user was already there when they
                        # hit `s`
                        print_status(interp, interp.next_expr[1])
                        LineEdit.reset_state(s)
                        return true
                    end
                end
                first = false
                command == "si" && break
                if !step_expr(interp)
                    interp = top_interp = done_stepping(s, interp; to_next_call = true)
                    LineEdit.reset_state(s)
                    return true
                end
            end
            command = "se"
        elseif command == "finish"
            finish!(interp)
            interp = top_interp = done_stepping(s, interp; to_next_call = true)
            LineEdit.reset_state(s)
            return true
        end
        if command == "bt"
            print_backtrace(top_interp)
            println()
            LineEdit.reset_state(s)
            return true
        elseif command == "shadow"
            print_shadowtree(interp.shadowtree, interp.next_expr[1])
            println()
            LineEdit.reset_state(s)
            return true
        elseif command == "linfo"
            eval(Main,:(linfo = $(get_linfo(interp))))
            LineEdit.transition(s, :abort)
            LineEdit.reset_state(s)
            return true
        elseif command == "ind"
            println("About to execute index", interp.next_expr[1])
            LineEdit.reset_state(s)
            return true
        elseif command == "loc"
            if interp.loctree == nothing
                print_with_color(:red, STDERR, "No loctree available\n")
                return true
            end
            w = create_widget(interp.loctree,interp.code)
            TerminalUI.print_snapshot(TerminalUI.InlineDialog(w,
                Base.Terminals.TTYTerminal("xterm", STDIN, STDOUT, STDERR)
                ))
            LineEdit.reset_state(s)
            return true
        elseif command == "up"
            new_stack_idx = length(top_interp.stack)-level
            if new_stack_idx == 0
                print_with_color(:red, STDERR, "Already at the top of the stack\n")
                return true
            end
            level += 1
            interp = top_interp.stack[new_stack_idx]
        elseif command == "down"
            new_stack_idx = length(top_interp.stack)-(level-2)
            if new_stack_idx > length(top_interp.stack)
                print_with_color(:red, STDERR, "Already at the bottom of the stack\n")
                return true
            end
            level -= 1
            interp = top_interp.stack[new_stack_idx]
        elseif command in ("ns","nc","n","se")
            if !can_step(interp)
                print_with_color(:red, STDERR, "Can't step in this frame\n")
                return true
            end
            (top_interp != interp) && (top_interp = finish_until!(top_interp, interp))
            level = 1
            try
                if command == "ns" ? !next_statement!(interp) :
                   command == "nc" ? !next_call!(interp) :
                   command == "n" ? !next_line!(interp) :
                    !step_expr(interp) #= command == "se" =#
                    interp = top_interp = done_stepping(s, interp; to_next_call = command == "n")
                    LineEdit.reset_state(s)
                    return true
                end
            catch err
                isa(err, Parser.Diagnostic) || rethrow(err)
                caught = false
                for interp_idx in length(top_interp.stack):-1:1
                    if process_exception!(top_interp.stack[interp_idx], err, interp_idx == length(top_interp.stack))
                        interp = top_interp = top_interp.stack[interp_idx]
                        resize!(top_interp.stack, interp_idx)
                        caught = true
                        break
                    end
                end
                !caught && rethrow(err)
                Main.JuliaParser.Parser.display_diagnostic(STDERR, interp.code, err)
                println(STDERR)
            end
        else
            unknown_command(interp, command)
        end
        if old_level != level
            panel.prompt = prompt(level,"debug")
            julia_prompt.prompt = prompt(level,"julia")
        end
        LineEdit.reset_state(s)
        print_status(interp)
        println()
        return true
    end

    const all_commands = ("q", "s", "si", "finish", "bt", "loc", "ind", "shadow",
        "up", "down", "ns", "nc", "n", "se")

    julia_prompt.on_done = (s,buf,ok)->begin
        if !ok
            LineEdit.transition(s, :abort)
            return false
        end
        xbuf = copy(buf)
        command = strip(takebuf_string(buf))
        res = try
            ts = Lexer.TokenStream{Lexer.SourceLocToken}(command)
            ts.filename = "REPL"
            res = Main.JuliaParser.Parser.parse(ts)
        catch e
            if !isa(e, Main.JuliaParser.Parser.Diagnostic)
                REPL.display_error(STDERR, err, Base.catch_backtrace())
            else
                Main.JuliaParser.Parser.display_diagnostic(STDERR, command, e)
            end
            REPL.println(STDERR); REPL.println(STDERR)
            return true
        end
        body = Lexer.¬(res)
        selfsym = symbol("#self#")  # avoid having 2 arguments called `#self#`
        unusedsym = symbol("#unused#")
        env = get_env_for_eval(interp)
        lnames = Any[interp.linfo.slotnames[2:end]..., interp.linfo.sparam_syms...]
        map!(x->(x===selfsym || !sym_visible(x) ? unusedsym : x), lnames)
        f = Expr(:->,Expr(:tuple,lnames...), body)
        lam = get_linfo(interp).module.eval(f)
        linfo = first(methods(lam)).func
        # New interpreter is on detached stack
        loctree, code = process_loctree(res, command, linfo, false)
        linfo = first(methods(lam)).func
        stmts = Base.uncompressed_ast(linfo)
        body = Expr(:body); body.args = stmts
        einterp = enter(linfo,body,env,Any[], loctree = loctree, code = code)
        try
            show(finish!(einterp))
            println(); println()
        catch err
            if isa(err, Parser.Diagnostic)
                Main.JuliaParser.Parser.display_diagnostic(STDOUT, command, err)
                println(STDOUT)
                LineEdit.reset_state(s)
                return true
            else
                REPL.display_error(STDERR, err, Base.catch_backtrace())
                REPL.println(STDERR); REPL.println(STDERR)
                # Convenience hack. We'll see if this is more useful or annoying
                for c in all_commands
                    !startswith(command, c) && continue
                    LineEdit.transition(s, panel)
                    LineEdit.state(s, panel).input_buffer = xbuf
                    break
                end
            end
        end
        LineEdit.reset_state(s)
        return true
    end

    const repl_switch = Dict{Any,Any}(
        '`' => function (s,args...)
            if isempty(s) || position(LineEdit.buffer(s)) == 0
                buf = copy(LineEdit.buffer(s))
                LineEdit.transition(s, julia_prompt) do
                    LineEdit.state(s, julia_prompt).input_buffer = buf
                end
            else
                LineEdit.edit_insert(s,key)
            end
        end
    )

    b = Dict{Any,Any}[skeymap, LineEdit.history_keymap, LineEdit.default_keymap, LineEdit.escape_defaults]
    panel.keymap_dict = LineEdit.keymap([repl_switch;b])
    julia_prompt.keymap_dict = LineEdit.keymap([Base.REPL.mode_keymap(panel);b])

    # Skip evaluated values (e.g. constants)
    done!(interp)
    print_status(interp)
    Base.REPL.run_interface(repl.t, LineEdit.ModalInterface([panel,julia_prompt,search_prompt]))
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
