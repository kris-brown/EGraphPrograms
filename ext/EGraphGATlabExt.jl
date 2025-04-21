""" Relating E-graphs to GATlab """
module EGraphGATlabExt

using EGraphPrograms, MLStyle, GATlab
import EGraphPrograms: extract, theory_programs, to_e_graph, saturate!, validate

# To upstream
#############

GATlab.getcontext(a::AlgAxiom) = a.localcontext

# Queries associated with debugging
###################################

""" All terms of a certain type, for debugging purposes """
function typed_terms(bk, G, ty)
  p = Program()
  reg = lookup!(p, ty)
  b = bind!(p, :typeof, reg)
  log!(p, (term=b,))
  res = interpret!(bk, p, G)
  return [extract(G, t) for (t,) in res]
end

""" All terms of a certain type, for debugging purposes """
function all_types(bk, G, ty)
  p = Program()
  reg = lookup!(p, ty)
  b = bind!(p, :sortof, reg)
  log!(p, (type=b,))
  res = interpret!(bk, p, G)
  return [extract(G, t) for (t,) in res]
end


"""
Any alg-axiom can be interpreted as a `Program` which looks for certain patterns
and executes a merge.
"""
function axiom_to_program(T::GAT, m::Ident; cache=Dict())
  a = getvalue(T[m])
  prog = Program()
  add_context!(T, prog, a.localcontext; cache)
  t1, t2 = a.equands # easily handle n-ary case later
  c1 = find_term!(prog, t1; cache)
  c2 = find_term!(prog, t2; cache)
  merge!(prog, c1, c2)
  log!(prog, (merge1=c1, merge2=c2))
  prog
end

""" 
Any term constructor can be interpreted as a `Program` which looks for a 
pattern and executes an addition to the egraph. It must also compute the type 
of the added term and add a `:typeof` relation. For example, for `compose`:

```
a <- typeof⁻¹(Ob)
b <- typeof⁻¹(Ob)
c <- typeof⁻¹(Ob)
f <- dom⁻¹(a) ∩ codom⁻¹(b)
g <- dom⁻¹(b) ∩ codom⁻¹(c)
fg = compose(f, g)
a_c = Hom(a, c)
ty = typeof(fg)
merge!(a_c, ty)
log(term = [7], type = a_c)
```
"""
function con_to_program(T::GAT, m::Ident; cache=Dict())
  tc = getvalue(T[m])
  prog = Program()
  add_context!(T, prog, tc.localcontext; cache)
  ctx = getidents(tc.localcontext)
  t = multiinsert!(prog, nameof(getdecl(tc)), Vector{Reg}(map(tc.args) do lid 
    cache[AlgTerm(ctx[lid.val])]
  end))
  typ = find_term!(prog, tc.type; cache, insert=true)
  typtrm = insert!(prog, :typeof, t)
  merge!(prog, typ, typtrm)
  log!(prog, (term=t, type=typ))
  prog
end

""" 
Any type constructor can be interpreted as a `Program` which looks for a 
pattern and executes an addition to the egraph. For example, `Hom` would result 
in a program like:

```
a <- typeof⁻¹(Ob)
b <- typeof⁻¹(Ob)

H = Hom(a,b)
s = sortof(H)
merge!(s, Hom)

h <- typeof⁻¹(H)
d = dom(H)
merge!(d,a)
c = codom(H)
merge!(c,b)
```

This creates type nodes which might not be in the image of `:typeof`. 
"""
function typecon_to_program(T::GAT, m::Ident; cache=Dict())
  tc = getvalue(T[m])
  prog = Program()
  add_context!(T, prog, tc.localcontext; cache)
  ctx = getidents(tc.localcontext)
  name = nameof(getdecl(tc))
  ty = multiapply!(prog, name, Vector{Reg}(map(tc.args) do lid 
    cache[AlgTerm(ctx[lid.val])]
  end))
  s = find_term!(prog, name; cache, insert=true)
  srttyp = insert!(prog, :sortof, ty)
  merge!(prog, s, srttyp)
  log!(prog, (sort=srttyp, type=ty))
  if !isempty(T.accessors[m])
    trm = bind!(prog, :typeof, ty)
    for (lid, a) in sort(collect(T.accessors[m]); by=first)
      areg = insert!(prog, nameof(getdecl(getvalue(T[a]))), trm)
      acc = AlgTerm(ident(tc.localcontext; lid=LID(lid)))
      merge!(prog, cache[acc], areg)
      log!(prog, (access_expr=areg, val=trm))
    end
  end
  prog
end


"""
Modifies a program to search add terms in a context and bind them to e-class 
ids. A dictionary from terms to e-class id (registers) is returned.
"""
function add_context!(T::GAT, prog::Program, ctx::TypeCtx; cache=Dict())
  for (trm, typ) in identvalues(ctx)
    b = bodyof(typ)
    b isa GATs.MethodApp || error("Bad assumption")
    n = nameof(headof(b))
    cache[AlgTerm(trm)] = if isempty(b.args)
      bind!(prog, :typeof, find_term!(prog, n; cache))
    else 
      args = find_term!.(Ref(prog), b.args; cache)
      acc = [nameof(getdecl(getvalue(T[a]))) 
             for (_, a) in sort(collect(T.accessors[methodof(b)]); by=first)]
      multibind!(prog, Dict(zip(acc, args)))      
    end
  end
end

""" 
Adds instructions to a program which will add a term (and all subterms) to an
egraph. Return a dictionary mapping AlgTerms to e-class ids.
"""
function find_term!(prog::Program, t::AlgAST; cache=Dict(), insert=false)
  haskey(cache, t) && return cache[t]
  AppIns! = insert ? multiinsert! : multiapply!
  res = @match t.body begin 
    A::Ident => 
      insert ? multiinsert!(prog, nameof(A), Reg[]) : lookup!(prog, nameof(A))
    A::GATs.MethodApp => 
      AppIns!(prog, nameof(A.head),
              Vector{Reg}(find_term!.(Ref(prog), A.args; cache)))
  end
  cache[t] = res
  res 
end

""" 
Add an instruction to a program `prog` which loads a particular symbol `t` (e.g.
`:Ob`) into a register, adding it to the e-graph if it doesn't exist.
"""
function find_term!(prog::Program, t::Symbol; cache=Dict(), insert=false)
  haskey(cache, t) && return cache[t]
  res = if insert 
    multiinsert!(prog, t, Reg[]) 
  else
    lookup!(prog, t)
  end
  
  cache[t] = res 
  res
end

"""
Any term in context can be turned into an e-graph with a distinguished e-class 
(the top-level term).
"""
function to_e_graph(T::GAT, b::EGraphBackend, G, t::TermInCtx)
  for (trm,typ) in identvalues(getcontext(t))
    trmtyp, _ = term_add(b, G, :(typeof($(strip_idents(toexpr(T, trm))))))
    ctyp = add_term!(T, b, G, typ)
    eclass_merge(b, G, trmtyp, ctyp)
  end
  add_term!(T, b, G, t.val)
end

function add_term!(T::GAT, b::EGraphBackend, eg, trm::AlgAST)
  x = toexpr(T, trm) |> strip_idents 
  term_add(b, eg, x) |> first
end

# TODO make it so we don't have to strip idents. Naive should work with more #
# generic types than :call Exprs # 
strip_idents(x::Ident) = nameof(x)
strip_idents(x::Symbol) = x
strip_idents(x::Expr) = @match x begin 
  Expr(:call, f, xs...) => Expr(:call, strip_idents(f), strip_idents.(xs)...)
  other => error("Unexpected expr $other")
end

function theory_programs(T::GAT; opt=false)
  # Annotate types / accessors
  typrogs = Dict(nameof(n)=>typecon_to_program(T,c) for (n,c) in typecons(T));
  # add terms based on term constructor rules
  tcprogs = Dict(nameof(n)=>con_to_program(T,c) for (n,c) in termcons(T));
  # quotient the e-graph by its axioms
  axprogs = Dict(map(T.axioms) do c
    n = nameof(c)
    (isnothing(n) ? Symbol(string(c.lid)) : n) => axiom_to_program(T,c) 
  end);
  # TODO combine the programs so that one runs a single one rather than multiple?
  return map([typrogs, tcprogs, axprogs]) do progs 
    NamedTuple(Dict(k => opt ? optimize(v) : v for (k,v) in progs))
  end
end

function extract(T::GAT, eg, e_class::Int) 
  exclude = [:typeof, :sortof]
  for tc in getvalue.(Ref(T), last.(typecons(T)))
    append!(exclude, nameof.(getcontext(tc)))
  end
  extract(eg, e_class, Dict(x=>10 for x in exclude))
end

""" 
Run tgds followed by egds for `gas` number of steps (or until one cycle adds 
no new enodes).

`optimize` will attempt to optimize the e-graph virtual machine programs
"""
function saturate!(bk::EGraphBackend, T::GAT, egraph; optimize=true, gas::Int=40)
  tys, tcs, axs = theory_programs(T; opt=optimize)


  for step in 1:gas
    allowed = Set(eclasses(egraph))
    @debug "SATURATE STEP: $step"
    change = false
    for (_, ty) in pairs(tys)
      for r in interpret!(bk, ty, egraph; allowed)
        change |= haskey(r,:newterm)
      end
    end
    for (_, tc) in pairs(tcs)
      for r in interpret!(bk, tc, egraph; allowed)
        change |= haskey(r,:newterm)
      end
    end
    # Quotient aggressively
    for qstep in 1:typemax(Int)
      println("quotient step $qstep") 
      ax_change = false 
      for (n, ax) in pairs(axs )
        println("Ax $n")
        for r in interpret!(bk, ax, egraph)
          c1, c2 = find!(egraph,r[:merge1]), find!(egraph,r[:merge2])
          c1 == c2 || println("$c1 $c2: $r")
          change |= (c1!=c2)
          ax_change |= (c1!=c2)
        end
      end
      ax_change || break
    end
    change && continue 
    println("E-saturation achieved in $step steps")
    return egraph 
  end
  @warn ("WARNING: did not saturate w/ $gas steps")
  return egraph 
end


# Validate GAT morphisms 
########################

validate(t::Module; kw...) = validate(t.MAP; kw...)


"""
Validate a map t: T → U by checking the axioms are provable
in U under the image of `t`.
"""
function validate(t::TheoryMap; gas=50)
  T, U = t.dom, t.codom
  b = NaiveBackend()
  all(T.axioms) do m
    ax = getvalue(T[m])
    Tctx = getcontext(ax)
    Tl, Tr = TermInCtx.(Ref(Tctx), ax.equands)
    Ul, Ur = t(Tl), t(Tr)
    G = EGraph()
    l_id = to_e_graph(U, b, G, Ul)
    r_id = to_e_graph(U, b, G, Ur)
    saturate!(b, U, G; gas)
    eq(G, l_id, r_id)
  end
end 


end # module
