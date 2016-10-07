__precompile__()
module ASTInterpreter

export enter, Environment, @enter
import Base: LineEdit, REPL

using AbstractTrees
using JuliaParser
using JuliaParser: Lexer, Tokens
using Base.Meta
import JuliaParser.Tokens: SourceNode, SourceRange, SourceExpr
using JuliaParser.Tokens: √
import JuliaParser.Diagnostics: diag, AbstractDiagnostic, display_diagnostic

import AbstractTrees: children, printnode

pretty_repr(x) = (string(x), :default)
pretty_repr(x::LineNumberNode) = (string("line: ", x.line), :red)
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
    ssavalues::Vector{Any}
    sparams::Vector{Any}
    # A vector from names to the slotnumber of that name
    # for which a reference was last encountered.
    last_reference::Dict{Symbol, Int}
end
Environment() = Environment(Vector{Nullable{Any}}(), Any[], Any[], Dict{Symbol, Int}())

Base.copy(e::Environment) = Environment(copy(e.locals), copy(e.ssavalues), copy(e.sparams), copy(e.last_reference))

type Interpreter
    stack::Vector{Any}
    env::Environment
    linfo::LambdaInfo
    evaluating_staged::Bool
    ast::Any
    it::Any
    cur_state::Any
    next_expr::Any
    shadowtree::Any
    code::AbstractString
    loctree::Any
    retval::Any
    exception_frames::Vector{Int}
    did_wrappercall::Bool
    prehook::AbstractString
end

function make_shadowtree(tree)
    resulttree = copy(tree)
    annotations = AbstractTrees.make_annotations(resulttree, resulttree, false) do node, parent, parent_ev
        if parent_ev
            return parent_ev
        end
        unevaluated = isa(node, Expr) || isa(node, GlobalRef) || isa(node, Symbol) || isa(node,Slot) ||
            isa(node,SSAValue) || isa(node, GotoNode) || isa(node, QuoteNode)
        if isa(node, Expr) && (node.head == :meta || node.head == :boundscheck ||
            node.head == :inbounds || node.head == :line)
            unevaluated = false
        end
        if (isa(node, SSAValue) || isa(node, Symbol) || isa(node, Slot) || isa(node,GlobalRef)) && isexpr(parent,:(=)) && parent.args[1] == node
            unevaluated = false
        end
        if isexpr(parent, :static_typeof)
            unevaluated = false
        end
        !unevaluated
    end
    shadowtree = AbstractTrees.ShadowTree(Tree(resulttree), Tree(annotations))
    it = indenumerate(PostOrderDFS(resulttree))
    shadowtree, it
end

using AbstractTrees: getnode

function enter(linfo, tree::Expr, env, stack = Any[];
        loctree = nothing, code = "", evaluating_staged = false)
    shadowtree, it = make_shadowtree(tree)

    interp = Interpreter(stack, env, linfo, evaluating_staged, tree, it,
        start(it), nothing, shadowtree, code, loctree, nothing, Vector{Int}(),
        false, "")
    push!(stack, interp)
    ind, node = next_expr!(interp)

    while getnode(interp.shadowtree,ind).shadow.x.val
        ind, node = next_expr!(interp)
    end

    interp
end
function enter(meth::Union{Method, TypeMapEntry}, env::Environment, stack = Any[]; kwargs...)
    isa(meth, TypeMapEntry) && (meth = meth.func)
    linfo = meth.lambda_template
    code = Base.uncompressed_ast(linfo)
    tree = Expr(:body); tree.args = code
    enter(linfo, tree, env, stack; kwargs...)
end
function enter(linfo::LambdaInfo, env::Environment, stack = Any[]; kwargs...)
    if linfo.inferred
        return enter(linfo.def, env, stack; kwargs...)
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
Tokens.normalize(x::ReplacementLoc) = x.replacing
Tokens.merge(x::ReplacementLoc,y::ReplacementLoc) =
    Tokens.merge(Tokens.normalize(x),Tokens.normalize(y))
Tokens.merge(x,y::ReplacementLoc) = Tokens.merge(x,Tokens.normalize(y))
Tokens.merge(x::ReplacementLoc,y::Void) = Tokens.merge(Tokens.normalize(x),y)
Tokens.merge(x::ReplacementLoc,y::Lexer.Token) = Tokens.merge(Tokens.normalize(x),y)
Tokens.merge(x::ReplacementLoc,y) = Tokens.merge(Tokens.normalize(x),y)

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

immutable Suppressed{T}
    item::T
end
Base.show(io::IO, x::Suppressed) = print(io, "<suppressed ", x.item, '>')

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

is_loc_meta(expr, kind) = isexpr(expr, :meta) && length(expr.args) >= 1 && expr.args[1] === kind

function determine_line_and_file(interp, highlight)
    file = get_linfo(interp).def.file
    line = get_linfo(interp).def.line
    foundline = false
    extra_locs = Any[]
    # Find a line number node previous to this expression
    if highlight !== nothing && !isempty(highlight)
        exprtree = interp.shadowtree.tree.x
        i = highlight[1]
        while i >= 1
            expr = exprtree.args[i]
            if !foundline && isa(expr, LineNumberNode)
                line = expr.line
                foundline = true
            elseif !foundline && isexpr(expr, :line)
                line = expr.args[1]
                foundline = true
            elseif foundline && is_loc_meta(expr, :push_loc)
                file = expr.args[2]
                extra_locs = determine_line_and_file(interp, [i-1])
                break
            elseif is_loc_meta(expr, :pop_loc)
                npops = 1
                while npops >= 1
                    i -= 1
                    expr = exprtree.args[i]
                    is_loc_meta(expr, :pop_loc) && (npops += 1)
                    is_loc_meta(expr, :push_loc) && (npops -= 1)
                end
            end
            i -= 1
        end
    end
    [extra_locs; (file, line)]
end

print_sourcecode(linfo::LambdaInfo, code, line) =
    print_sourcecode(code, line, linfo.def.file, linfo.def.line; file = SourceFile(code))
function print_sourcecode(code, line, deffile, defline; file = SourceFile(code))
    startoffset, stopoffset = compute_source_offsets(code, file.offsets[line],
        max(1,file == deffile ? defline : line-1), line+3; file=file)

    if startoffset == -1
        print_with_color(:bold, STDOUT, "Line out of file range (bad debug info?)")
        return
    end

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

    print_with_color(:bold, STDOUT,
        string("In ", deffile,":",defline, "\n"))

    for textline in code
        print_with_color(lineno == current_line ? :yellow : :bold,
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
    if offsetline - 3 > length(file.offsets) || startline > length(file.offsets)
        return -1, -1
    end
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

print_status(state, _::Void, args...) = nothing
function print_status(state, interp::Interpreter, highlight = idx_stack(interp); fancy = fancy_mode)
    if !fancy && !isempty(interp.code)
        fls = determine_line_and_file(interp, highlight)
        for (file,line) in fls[end:-1:2]
            # See if we can get the code for this
            dfile = Base.find_source_file(string(file))
            file = dfile == nothing ? file : dfile
            contents = readfileorhist(file)
            file = "macro expansion from $file"
            if contents == nothing
                print_with_color(:bold, STDOUT,
                    string("In ", file,":",line, "\n"))
                continue
            end
            print_sourcecode(contents, line, file, max(1,line-3))
        end
        print_sourcecode(interp.linfo, interp.code, fls[1][2])
        ex = interp.shadowtree[highlight].tree.x
        # print slots with their names
        wrap = !isa(ex,Expr)
        ex = wrap ? Expr(:block, ex) : copy(ex)
        treemap!(function (x)
                     if isa(x, Slot)
                         name = interp.linfo.slotnames[x.id]
                         return sym_visible(name) ? name : x
                     elseif isa(x, AbstractArray)
                         return length(x) <= 10 ? x : Suppressed(summary(x))
                     elseif isa(x, LambdaInfo)
                         return Suppressed("generated thunk")
                     else
                         return x
                     end
                 end,
                 PreOrderDFS(ex,node->isa(node, Expr)))
        nargs = length(ex.args)
        # Suppress arguments that are too long
        for (i, arg) in enumerate(ex.args)
            nbytes = length(repr(arg))
            if nbytes > max(40, div(200,nargs))
                ex.args[i] = Suppressed("$nbytes bytes of output")
            end
        end
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
    interp.next_expr = get(x[1]), x[2]
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

    next_state  = typeof(interp.cur_state)(
        AbstractTrees.ImplicitNodeStack(Any[],
            AbstractTrees.ImplicitIndexStack([lind]))
    )

    # next_expr! below will move past the label node
    interp.cur_state = next(interp.it, next_state)[2]
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
        if isa(node, Slot) || isa(node,SSAValue)
            # Check if we're the LHS of an assignment
            if ind.idx_stack.stack[end] == 1 && interp.shadowtree.tree[ind.idx_stack.stack[1:end-1]].head == :(=)
                ret = node
            elseif isa(node,SSAValue)
                ret = interp.env.ssavalues[node.id+1]
            else
                nslots = length(interp.env.locals)
                id = node.id
                interp.env.last_reference[interp.linfo.slotnames[id]] = id
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
                if isa(lhs, SSAValue)
                    interp.env.ssavalues[lhs.id+1] = rhs
                elseif isa(lhs, Slot)
                    interp.env.locals[lhs.id] = Nullable{Any}(rhs)
                    interp.env.last_reference[interp.linfo.slotnames[lhs.id]] =
                        lhs.id
                elseif isa(lhs, GlobalRef)
                    eval(lhs.mod,:($(lhs.name) = $(QuoteNode(rhs))))
                end
                # Special case hack for readability.
                # ret = rhs
                ret = node
            elseif node.head == :&
                ret = node
            elseif node.head == :gotoifnot
                ret = node
                if !isa(node.args[1], Bool)
                    throw(TypeError(interp.linfo.def.name, "if", Bool, node.args[1]))
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
                        if isa(node.args[i], Union{Symbol,SSAValue,Slot,GlobalRef})
                            node.args[i] = QuoteNode(node.args[i])
                        end
                    end
                    ret = eval(node)
                elseif isa(f, LambdaInfo)
                    ret = finish!(enter_call_expr(interp, node))
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
        diag(D, Tree(interp.loctree)[ind.idx_stack.stack].loc, "while running this expression", :note)
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

function changed_line!(expr, line, fls)
    if length(fls) == 1 && isa(expr, LineNumberNode)
        return expr.line != line
    elseif length(fls) == 1 && isa(expr, Expr) && isexpr(expr, :line)
        return expr.args[1] != line
    else
        if is_loc_meta(expr, :pop_loc)
            pop!(fls)
        elseif is_loc_meta(expr, :push_loc)
            push!(fls,(expr.args[2],0))
        end
        return false
    end
end

isgotonode(node) = isa(node, GotoNode) || isexpr(node, :gotoifnot)

"""
Determine whether we are calling a function for which the current function
is a wrapper (either because of optional arguments or becaue of keyword arguments).
"""
function iswrappercall(interp, expr)
    !isexpr(expr, :call) && return false
    r = determine_method_for_expr(interp, expr; enter_generated = false)
    if r !== nothing
        linfo, method, args, _ = r
        ours, theirs = interp.linfo.def, method
        # Check if this a method of the same function that shares a definition line/file.
        # If so, we're likely in an automatically generated wrapper.
        if ours.sig.parameters[1] == theirs.sig.parameters[1] &&
            ours.line == theirs.line && ours.file == theirs.file
            return true
        end
    end
    return false
end

function next_line!(interp; state = nothing)
    didchangeline = false
    fls = determine_line_and_file(interp, idx_stack(interp))
    line = fls[1][2]
    first = true
    while !didchangeline
        ind, node = interp.next_expr
        # Skip evaluated values (e.g. constants)
        while interp.shadowtree.shadow[ind].val
            didchangeline = changed_line!(node, line, fls)
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
            fls = determine_line_and_file(interp, idx_stack(interp))
            didchangeline = line != fls[1][2]
        elseif iswrappercall(interp, node)
            interp.did_wrappercall = true
            interp = enter_call_expr(interp, node)
        else
            _step_expr(interp) || return false
        end
    end
    if state !== nothing && interp != state.interp
        state.interp = state.top_interp = interp
    end
    done!(interp)
    # Ok, we stepped to the next line. Now step through to the next call
    call_or_assignment(node) = isexpr(node,:call) || isexpr(node,:(=)) || isexpr(node, :return)
    call_or_assignment(interp.next_expr[2]) ||
        next_until!(call_or_assignment, interp)
end

function advance_to_line(interp, line)
    while true
        at_line = determine_line_and_file(interp, idx_stack(interp))[1][2]
        at_line == line && break
        next_line!(interp) || break
    end
end

function _evaluated!(interp, ret, wasstaged = false)
    if wasstaged
        # If this is the result of a staged function, we replace the argument
        # the call rather than the call itself
        ind, node = interp.next_expr
        @assert isexpr(node, :call)
        interp.shadowtree[[ind.idx_stack.stack; 1]] = (ret, AnnotationNode{Any}(true,AnnotationNode{Any}[]))
    else
        ind, node = interp.next_expr
        interp.shadowtree[ind.idx_stack.stack] = (ret, AnnotationNode{Any}(true,AnnotationNode{Any}[]))
    end
end
evaluated!(interp, ret, wasstaged = false) = (_evaluated!(interp, ret, wasstaged); done!(interp))

"""
Advance to the next evaluatable statement
"""
function done!(interp)
    ind, node = interp.next_expr
    # Skip evaluated values (e.g. constants)
    while interp.shadowtree.shadow[ind.idx_stack.stack].val
        ind, node = next_expr!(interp)
    end
    return true
end

function to_function(x)
    if isa(x, Function) || isa(x, Core.IntrinsicFunction)
        x
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
            push!(theassignments, (loc, nothing))                  # ssavalue() = next()
            push!(theassignments, (loc, nothing))        # ssavalue() = ans.1
            push!(theassignments, (loc, nothing))        # ssavalue() = ans.2
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
    if loweredast == nothing
        println("Failed to lower expression")
        return
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
    parsedexpr = Lexer.¬(res)
    parsedloc = Lexer.√(res)
    loweredast = nothing
    local thecalls, theassignments, forlocs
    loctree = try
        res = lower!(res)
        parsedexpr = Lexer.¬(res)
        parsedloc = Lexer.√(res)
        stmts = Base.uncompressed_ast(linfo)
        loweredast = Expr(:body); loweredast.args = stmts
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
        loctree = SourceNode(Tokens.normalize(reduce(⤄,PostOrderDFS(parsedloc))),loctree.children)
    end

    loctree, contents
end

const SEARCH_PATH = [joinpath(JULIA_HOME,"../share/julia/base/"),
    joinpath(JULIA_HOME,"../include/")]
function readfileorhist(file)
    if startswith(string(file),"REPL[")
        hist_idx = parse(Int,string(file)[6:end-1])
        isdefined(Base, :active_repl) || return nothing, ""
        hp = Base.active_repl.interface.modes[1].hist
        return hp.history[hp.start_idx+hist_idx]
    else
        for path in SEARCH_PATH
            fullpath = joinpath(path,string(file))
            if isfile(fullpath)
                return open(readstring, fullpath)
            end
        end
    end
    return nothing
end

function reparse_meth(meth)
    if isa(meth, LambdaInfo)
        meth = meth.def
    elseif isa(meth, TypeMapEntry)
        meth = meth.func
    end
    file, line = Base.find_source_file(string(meth.file)), meth.line
    contents = readfileorhist(file == nothing ? meth.file : file)
    contents == nothing && return (nothing, "")
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
    process_loctree(res, contents, meth)
end

function prepare_locals(linfo, argvals = ())
    linfo = linfo.def.lambda_template
    # Construct the environment from the arguments
    argnames = linfo.slotnames[1:linfo.nargs]
    locals = Array(Nullable{Any}, length(linfo.slotflags))
    ng = isa(linfo.ssavaluetypes, Int) ? linfo.ssavaluetypes : length(linfo.ssavaluetypes)
    ssavalues = Array(Any, ng)
    sparams = Array(Any, length(linfo.sparam_syms))
    for i = 1:linfo.nargs
        if linfo.isva && i == length(argnames)
            locals[i] = length(argvals) >= i ? tuple(argvals[i:end]...) : Nullable{Any}(())
            break
        end
        locals[i] = length(argvals) >= i ? Nullable{Any}(argvals[i]) : Nullable{Any}()
    end
    # add local variables initially undefined
    for i = (linfo.nargs+1):length(linfo.slotnames)
        locals[i] = Nullable{Any}()
    end
    Environment(locals, ssavalues, sparams, Dict{Symbol,Int}())
end

function determine_method_for_expr(interp, expr; enter_generated = false)
    f = to_function(expr.args[1])
    allargs = expr.args
    # Extract keyword args
    local kwargs = Expr(:parameters)
    if length(allargs) > 1 && isexpr(allargs[2], :parameters)
        kwargs = splice!(allargs, 2)
    end
    if !isempty(kwargs.args)
        of = f
        f = Core.kwfunc(f)
        allargs = [f,reduce(vcat,Any[[ex.args[1];ex.args[2]] for ex in kwargs.args]),of,
            allargs[2:end]...]
    elseif is(f,Core._apply)
        f = to_function(allargs[2])
        allargs = Base.append_any((allargs[2],), allargs[3:end]...)
    end
    # Can happen for thunks created by generated functions
    if !isa(f, Core.Builtin) && !isa(f, Core.IntrinsicFunction)
        args = allargs[2:end]
        argtypes = Tuple{map(_Typeof,args)...}
        if isa(f, LambdaInfo)
            linfo = f
            method = linfo.def
            enter_generated = false
            lenv = linfo.sparam_vals
        else
            method = try
                which(f, argtypes)
            catch err
                @show typeof(f)
                println(f)
                println(argtypes)
                rethrow(err)
            end
            argtypes = Tuple{_Typeof(f), argtypes.parameters...}
            args = allargs
            sig, tvars = method.sig, method.tvars
            isa(method, TypeMapEntry) && (method = method.func)
            linfo = method.lambda_template
            # Get static parameters
            (ti, lenv) = ccall(:jl_match_method, Any, (Any, Any, Any),
                               argtypes, sig, tvars)::SimpleVector
            if method.isstaged && !enter_generated
                # If we're stepping into a staged function, we need to use
                # the specialization, rather than stepping thorugh the
                # unspecialized method.
                linfo = Core.Inference.specialize_method(method, argtypes, lenv, false)
            else
                if method.isstaged
                    args = map(_Typeof, args)
                end
            end
        end
        return linfo, method, args, lenv
    end
    nothing
end

function enter_call_expr(interp, expr; enter_generated = false)
    r = determine_method_for_expr(interp, expr; enter_generated = enter_generated)
    if r !== nothing
        linfo, method, args, lenv = r
        loctree, code = nothing, ""
        if !(method.isstaged && !enter_generated)
            loctree, code = reparse_meth(method)
        end
        env = prepare_locals(linfo, args)
        # Add static parameters to environment
        for i = 1:length(lenv)
            env.sparams[i] = lenv[i]
        end
        newinterp = enter(method.isstaged && !enter_generated ? linfo : method,
            env, interp != nothing ? interp.stack : Any[],
            loctree = loctree, code = code,
            evaluating_staged = method.isstaged && enter_generated)
        return newinterp
    end
    nothing
end

function print_linfo_desc(io::IO, linfo, specslottypes = false)
    slottypes = linfo.slottypes
    linfo = linfo.def.lambda_template
    argnames = linfo.slotnames[2:linfo.nargs]
    spectypes = specslottypes && (slottypes != nothing) ?
        slottypes[2:linfo.nargs] : Any[Any for i=1:length(argnames)]
    print(io, linfo.def.name,'(')
    first = true
    for (argname, argT) in zip(argnames, spectypes)
        first || print(io, ", ")
        first = false
        print(io, argname)
        !is(argT, Any) && print(io, "::", argT)
    end
    print(io, ") at ",linfo.def.file,":",linfo.def.line)
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
            T = typeof(val)
            val = repr(val)
            if length(val) > 150
                val = Suppressed("$(length(val)) bytes of output")
            end
            println(io, name, "::", T, " = ", val)
        end
    end
end

function print_locals(io::IO, linfo, env::Environment, undef_callback)
    linfo = linfo.def.lambda_template
    for i = 1:length(env.locals)
        print_var(io, linfo.slotnames[i], env.locals[i], undef_callback)
    end
    for i = 1:length(env.sparams)
        print_var(io, linfo.sparam_syms[i], Nullable{Any}(env.sparams[i]), undef_callback)
    end
end

function print_backtrace(state, interp)
    num = 1
    for frame in reverse(interp.stack)
        print_frame(state, STDOUT, num, frame)
        num += 1
    end
end

function print_frame(_, io::IO, num, interp::Interpreter)
    print(io, "[$num] ")
    print_linfo_desc(io, interp.linfo)
    println(io)
    print_locals(io, interp.linfo, interp.env,
        (io,name)->println(io, "<undefined>"))
end
print_backtrace(_::Void) = nothing

include(joinpath(dirname(@__FILE__),"..","..","JuliaParser","src","interactiveutil.jl"))

get_env_for_eval(interp::Interpreter) = interp.env
get_linfo(interp::Interpreter) = interp.linfo

function execute_command(interp, command)
    print_with_color(:red,"\nUnknown command!\n");
end

execute_command(state, interp, cmd1, command) = (execute_command(interp, command); return false)

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

function process_exception!(interp::Interpreter, D::AbstractDiagnostic, istop)
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

function eval_in_interp(interp, body, slbody = nothing, code = "")
    selfsym = Symbol("#self#")  # avoid having 2 arguments called `#self#`
    unusedsym = Symbol("#unused#")
    env = get_env_for_eval(interp)
    linfo = get_linfo(interp)
    lnames = Any[linfo.slotnames[2:end]..., linfo.sparam_syms...]
    map!(x->(x===selfsym || !sym_visible(x) ? unusedsym : x), lnames)
    lnames = unique(lnames)
    f = Expr(:->,Expr(:tuple,lnames...), body)
    lam = linfo.def.module.eval(f)
    linfo = first(methods(lam)).lambda_template
    # New interpreter is on detached stack
    loctree = nothing
    if slbody != nothing
        loctree, code = process_loctree(slbody, code, linfo, false)
    end
    # Construct a new environment with the arguments inserted
    eval_env = ASTInterpreter.prepare_locals(linfo)
    for varname in lnames
        lidx = findfirst(linfo.slotnames, varname)
        lidx == 0 && continue
        if haskey(env.last_reference, varname)
            eval_env.locals[lidx] = env.locals[env.last_reference[varname]]
        else
            oldidx = findfirst(get_linfo(interp).slotnames, varname)
            if oldidx == 0
                sparamidx = findfirst(get_linfo(interp).sparam_syms, varname)
                sparamidx == 0 && continue
                eval_env.locals[lidx] = env.sparams[sparamidx]
            else
                eval_env.locals[lidx] = env.locals[oldidx]
            end
        end
    end
    stmts = Base.uncompressed_ast(linfo)
    body = Expr(:body); body.args = stmts
    einterp = enter(linfo,body,eval_env,Any[], loctree = loctree, code = code)
    ok, val = try
        true, finish!(einterp)
    catch err
        false, err
    end
    # Here we would reapply the variables
    ok, val
end

type InterpreterState
    top_interp
    interp
    level
    s
    julia_prompt
    main_mode
end

function make_linfo(method, ret)
    func = method.lambda_template
    argnames = [func.slotnames[i] for i = 1:func.nargs]
    lambda = Expr(:lambda, argnames, Expr(Symbol("scope-block"), Expr(:block, ret)))
    if !isempty(func.sparam_syms)
        lambda = Expr(Symbol("with-static-parameters"), lambda, func.sparam_syms...)
    end
    linfo = eval(method.module, lambda)
    linfo.def = method
    linfo
end


# Command Implementation
function done_stepping!(state, interp; to_next_call = false)
    s = state.s
    stack = state.interp.stack
    this_idx = findfirst(stack, interp)
    if this_idx == 0
        LineEdit.transition(s, :abort)
        interp = nothing
    else
        oldinterp = state.interp
        state.top_interp = state.interp = this_idx == 1 ? nothing : stack[this_idx-1]
        resize!(stack, this_idx-1)
        if !isa(state.interp, Interpreter)
            LineEdit.transition(s, :abort)
            return nothing
        end
        ret = oldinterp.retval
        if oldinterp.evaluating_staged
            ret = make_linfo(get_linfo(oldinterp).def, oldinterp.retval)
        end
        evaluated!(state.interp, ret, oldinterp.evaluating_staged)
        # For wrappercall, also pop the wrapper
        if to_next_call && state.interp.did_wrappercall
            finish!(state.interp)
            done_stepping!(state, state.interp; to_next_call = to_next_call)
            return interp
        end
        to_next_call &&
          (isexpr(state.interp.next_expr[2], :call) || next_call!(state.interp))
    end
    interp
end

function execute_command(state, interp::Interpreter, ::Val{:?}, cmd)
    display(
            Base.@md_str """
    Basic Commands:\\
    - `n` steps to the next line\\
    - `s` steps into the next call\\
    - `finish` runs to the end of the function\\
    - `bt` shows a simple backtrace\\
    - ``` `stuff ``` runs `stuff` in the current frame's context\\
    - `fr v` will show all variables in the current frame\\
    - `f n` where `n` is an integer, will go to the `n`-th frame.

    Advanced commands:\\
    - `nc` steps to the next call\\
    - `ns` steps to the next statement\\
    - `se` does one expression step\\
    - `si` does the same but steps into a call if a call is the next expression\\
    - `sg` steps into a generated function\\
    - `shadow` shows the internal representation of the expression tree\\
       (for debugger debugging only)\\
    - `loc` shows the column data for the current top frame,\\
        in the same format as JuliaParsers's testshell.\\
    """)
    return false
end

function execute_command(state, interp::Interpreter, ::Val{:finish}, cmd)
    finish!(state.interp)
    done_stepping!(state, state.interp; to_next_call = true)
    return true
end

function execute_command(state, interp::Interpreter, ::Val{:edit}, cmd)
    file, line = determine_line_and_file(interp, idx_stack(interp))[end]
    dfile = Base.find_source_file(string(file))
    file = dfile == nothing ? file : dfile
    Base.edit(file, line)
    return false
end

function execute_command(state, interp, ::Val{:bt}, cmd)
    print_backtrace(state, state.top_interp)
    println()
    return false
end

function execute_command(state, interp::Interpreter, ::Val{:shadow}, cmd)
    print_shadowtree(interp.shadowtree, idx_stack(interp))
    println()
    return false
end

function execute_command(state, interp, ::Val{:linfo}, cmd)
    eval(Main,:(linfo = $(get_linfo(interp))))
    LineEdit.transition(state.s, :abort)
    return false
end

function execute_command(state, interp::Interpreter, ::Val{:ind}, cmd)
    println("About to execute index ", idx_stack(interp))
    return false
end

function execute_command(state, interp::Interpreter, ::Val{:loc}, cmd)
    if interp.loctree == nothing
        print_with_color(:red, STDERR, "No loctree available\n")
        return true
    end
    w = create_widget(state.interp.loctree, state.interp.code)
    TerminalUI.print_snapshot(TerminalUI.InlineDialog(w,
        Base.Terminals.TTYTerminal("xterm", STDIN, STDOUT, STDERR)
        ))
    return false
end

function execute_command(state, interp, ::Val{:up}, cmd)
    new_stack_idx = length(state.top_interp.stack)-state.level
    if new_stack_idx == 0
        print_with_color(:red, STDERR, "Already at the top of the stack\n")
        return false
    end
    state.level += 1
    state.interp = state.top_interp.stack[new_stack_idx]
    return true
end

function execute_command(state, interp, ::Val{:down}, cmd)
    new_stack_idx = length(state.top_interp.stack)-(state.level-2)
    if new_stack_idx > length(state.top_interp.stack)
        print_with_color(:red, STDERR, "Already at the bottom of the stack\n")
        return false
    end
    state.level -= 1
    state.interp = state.top_interp.stack[new_stack_idx]
    return true
end

function execute_command(state, interp, ::Union{Val{:f},Val{:fr}}, command)
    subcmds = split(command,' ')[2:end]
    if isempty(subcmds) || subcmds[1] == "v"
        print_frame(state, STDOUT, state.level, state.interp)
        return false
    else
        new_level = parse(Int, subcmds[1])
        new_stack_idx = length(state.top_interp.stack)-(new_level-1)
        if new_stack_idx > length(state.top_interp.stack) || new_stack_idx < 1
            print_with_color(:red, STDERR, "Not a valid frame index\n")
            return false
        end
        state.level = new_level
        state.interp = state.top_interp.stack[new_stack_idx]
    end
    return true
end

function execute_command(state, interp::Interpreter, cmd::Union{Val{:s},Val{:si},Val{:sg}}, command)
    first = true
    while true
        expr = state.interp.next_expr[2]
        if isa(expr, Expr)
            if expr.head == :call && !isa(expr.args[1],Core.IntrinsicFunction)
                x = enter_call_expr(state.top_interp, expr, enter_generated = command == "sg")
                if x !== nothing
                    state.interp = state.top_interp = x
                    (cmd == Val{:s}() || cmd == Val{:sg}()) && next_call!(x)
                    return true
                end
            elseif !first && isexpr(expr, :return)
                # As a special case, do not step through a return
                # statement, unless the user was already there when they
                # hit `s`
                return true
            end
        end
        first = false
        command == "si" && break
        if !step_expr(state.interp)
            done_stepping!(state, state.top_interp; to_next_call = true)
            return true
        end
    end
    execute_command(state, interp, Val{:se}(), "se")
end

function execute_command(state, interp::Interpreter, ::Union{Val{:ns},Val{:nc},Val{:n},Val{:se}}, command)
    (state.top_interp != interp) && (state.top_interp = finish_until!(state.top_interp, interp))
    state.level = 1
    if command == "ns" ? !next_statement!(state.interp) :
       command == "nc" ? !next_call!(state.interp) :
       command == "n" ? !next_line!(state.interp; state = state) :
        !step_expr(state.interp) #= command == "se" =#
        done_stepping!(state, state.interp; to_next_call = command == "n")
        return true
    end
    return true
end

function eval_code(state, command)
    local theerr = nothing
    res = try
        ts = Lexer.TokenStream{Lexer.SourceLocToken}(command)
        ts.filename = "REPL"
        res = Main.JuliaParser.Parser.parse(ts)
    catch err
        theerr = err
    end
    if theerr == nothing
        body = Lexer.¬(res)
        ok, result = eval_in_interp(state.interp, body, res, command)
        ok && return (ok, result)
        theerr = result
    end
    if !isa(theerr, AbstractDiagnostic)
        REPL.display_error(STDERR, theerr, Base.catch_backtrace())
    else
        display_diagnostic(STDERR, command, theerr)
    end
    REPL.println(STDERR); REPL.println(STDERR)
    return false, nothing
end
eval_code(state, buf::IOBuffer) = eval_code(state, takebuf_string(buf))

function language_specific_prompt(state, stack::Interpreter)
    state.julia_prompt
end

function run_pre_hooks(state, interp::Interpreter)
    if !isempty(interp.prehook)
        ok, res = eval_code(state, interp.prehook)
        ok && res !== nothing && (display(res); println())
    end
end
run_pre_hooks(state, interp) = nothing

function execute_command(state, interp::Interpreter, ::Val{:prehook}, cmd)
    idx = findfirst(cmd, ' ')
    cmd = idx == 0 ? "" : cmd[idx+1:end]
    interp.prehook = cmd
    return false
end

function RunDebugREPL(top_interp)
    promptname(level, name) = "$level|$name > "

    repl = Base.active_repl
    state = InterpreterState(top_interp, top_interp, 1, nothing, nothing, nothing)

    # Setup debug panel
    panel = LineEdit.Prompt(promptname(state.level, "debug");
        prompt_prefix="\e[38;5;166m",
        prompt_suffix=Base.text_colors[:white],
        on_enter = s->true)

    # For now use the regular REPL completion provider
    replc = Base.REPL.REPLCompletionProvider(repl)

    # Set up the main Julia prompt
    julia_prompt = LineEdit.Prompt(promptname(state.level, "julia");
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


    state.interp = top_interp
    state.julia_prompt = julia_prompt
    state.main_mode = panel

    panel.on_done = (s,buf,ok)->begin
        state.s = s
        line = takebuf_string(buf)
        old_level = state.level
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
        do_print_status = true
        cmd1 = split(command,' ')[1]
        do_print_status = try
            execute_command(state, state.interp, Val{Symbol(cmd1)}(), command)
        catch err
            isa(err, AbstractDiagnostic) || rethrow(err)
            caught = false
            for interp_idx in length(state.top_interp.stack):-1:1
                if process_exception!(state.top_interp.stack[interp_idx], err, interp_idx == length(top_interp.stack))
                    interp = state.top_interp = state.top_interp.stack[interp_idx]
                    resize!(state.top_interp.stack, interp_idx)
                    caught = true
                    break
                end
            end
            !caught && rethrow(err)
            display_diagnostic(STDERR, state.interp.code, err)
            println(STDERR)
            LineEdit.reset_state(s)
            return true
        end
        if old_level != state.level
            panel.prompt = promptname(state.level,"debug")
            julia_prompt.prompt = promptname(state.level,"julia")
        end
        LineEdit.reset_state(s)
        if do_print_status
            print_status(state, state.interp)
            run_pre_hooks(state, state.interp)
        end
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
        ok, result = eval_code(state, buf)
        if ok
            display(result)
            println(); println()
        else
            command = takebuf_string(buf)
            # Convenience hack. We'll see if this is more useful or annoying
            for c in all_commands
                !startswith(command, c) && continue
                LineEdit.transition(s, panel)
                LineEdit.state(s, panel).input_buffer = xbuf
                break
            end
        end
        LineEdit.reset_state(s)
        return true
    end

    const repl_switch = Dict{Any,Any}(
        '`' => function (s,args...)
            if isempty(s) || position(LineEdit.buffer(s)) == 0
                prompt = language_specific_prompt(state, state.interp)
                buf = copy(LineEdit.buffer(s))
                LineEdit.transition(s, prompt) do
                    LineEdit.state(s, prompt).input_buffer = buf
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
    done!(state.interp)
    print_status(state, state.interp)
    Base.REPL.run_interface(repl.t, LineEdit.ModalInterface([panel,julia_prompt,search_prompt]))
end

idx_stack(interp::Interpreter) = interp.next_expr[1].idx_stack.stack

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
                        print_step && print_shadowtree(interp.shadowtree, idx_stack(interp))
                        continue
                    end
                end
            end
        end
        if !step_expr(interp)
            break
        end
        print_step && print_shadowtree(interp.shadowtree, idx_stack(interp))
    end
    interp.retval
end

macro enter(arg)
    arg = ASTInterpreter.lower!(arg)
    @assert isa(arg, Expr) && arg.head == :call
    quote
        theargs = $(esc(Expr(:tuple,map(
            x->isexpr(x,:parameters)?QuoteNode(x):x,arg.args)...)))
        interp = ASTInterpreter.enter_call_expr(nothing,Expr(:call,theargs...))
        ASTInterpreter.next_call!(interp)
        ASTInterpreter.RunDebugREPL(interp)
    end
end

include("lowering.jl")
include("precompile.jl")
_precompile_()

end
