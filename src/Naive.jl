""" Naive implementation of E-Graphs """
module Naive
export EGraph, CallExpr, find!, add!, rebuild!, eq, NaiveBackend, find_root!, 
       EId, nterms, nclasses

using MLStyle, DataStructures, StructEquality

import DataStructures: find_root, find_root!
using ..EGraphInterface
import ..EGraphInterface: init_egraph, eterm_head,eterm_children, eterm_apply, 
  extract_term, eclass_root, eterms, eterm_lookup, term_lookup, eclass_merge, 
  eterm_add, term_add, eclasses

const Expr0 = Union{Symbol, Expr}

"""
An index into the union-find data structure component of an E-graph. Each
e-class is associated to a set of EIds, including a canonical one. This set is
stored by the union-find (`eqrel` field in `EGraph`).
"""
const EId = Int 

"""
E-term data structure: head is a symbol but children are e-class IDs.
"""
@struct_hash_equal struct CallExpr
  head::Symbol
  body::Vector{EId}
  CallExpr(f::Symbol, body=EId[]) = new(f, body)
end

function Base.show(io::IO, c::CallExpr)
  print(io, c.head)
  if !isempty(c.body)
    print(io, "(")
    for (i, arg) in enumerate(c.body)
      print(io, arg)
      i == length(c.body) || print(io, ", ")
    end
    print(io, ")")
  end

end

# in general, we want to support anything which implements TermInterface
const ETerm = CallExpr 

const Parents = Dict{ETerm, EId}

head(c::CallExpr) = c.head
children(c::CallExpr) = c.body
Base.length(c::CallExpr) = length(children(c))

"""
`reps` A representation of an equivalence class of e-terms. 
`parents` caches all the e IDs which directly refer to a given term (as opposed 
to some reference in a nested term)
"""
mutable struct EClass
  reps::Set{ETerm}
  parents::Parents
  function EClass(reps::Set{ETerm}, parents::Parents=Parents())
    new(reps, parents)
  end
end

Base.length(e::EClass) = length(e.reps)

Base.iterate(e::EClass) = iterate(e.reps)

Base.iterate(e::EClass, i) = iterate(e.reps, i)

function add_parent!(ec::EClass, etrm::ETerm, i::EId)
  ec.parents[etrm] = i
end


"""
Stores a congruent partial equivalence relation on terms.

`eqrel` is an equivalence relation on eclass ids
`eclasses` sends each eclass id to its `EClass` data
`hashcons` assigns each eterm an eclass id 
`worklist` - e-class ids which have been merged but not yet rebuilt
`isclean` - is the Egraph safe to read from
"""
struct EGraph
  eqrel::IntDisjointSets{EId}
  eclasses::Dict{EId, EClass}
  hashcons::Dict{ETerm, EId}
  worklist::Vector{EId}
  isclean::Ref{Bool}
  function EGraph()
    new(IntDisjointSets{EId}(0), Dict{EId, EClass}(),
        Dict{ETerm, EId}(), EId[], Ref(true))
  end
end

nterms(e::EGraph) = sum(nterms(e, c) for c in keys(e.eclasses); init=0)

nterms(e::EGraph, i::EId) = length(e[i].reps)

nclasses(e::EGraph) = length(e.eclasses)

Base.length(e::EGraph) = nclasses(e)

find_root!(eg::EGraph, e::EId) = find_root!(eg.eqrel, e)

find_root(eg::EGraph, e::EId) = find_root!(eg.eqrel, e)

Base.getindex(eg::EGraph, e::EId) = eg.eclasses[e]

Base.getindex(eg::EGraph, e::ETerm) = eg.hashcons[e]

Base.getindex(eg::EGraph, e::Expr0) = add!(eg, e)

Base.haskey(eg::EGraph, e::EId) = haskey(eg.eclasses,e)

Base.haskey(eg::EGraph, e::ETerm) = haskey(eg.hashcons, e)

"""
Update e-term to refer to canonical e-ids
"""
function canonicalize!(eg::EGraph, etrm::ETerm)
  ETerm(head(etrm), find_root!.(Ref(eg.eqrel), children(etrm)))
end

"""
Get the e-class id of a raw term (not an e-term). Add the term if not present.
"""
add!(eg::EGraph, expr::Expr0) = @match expr begin
  f::Symbol => add!(eg, CallExpr(f))
  Expr(:call, f, xs...) =>  begin 
    args = add!.(Ref(eg), xs)
    add!(eg, CallExpr(f, args))
end
  _ => error("bad CallExpr $eg")
end

""" Add eterm to an egraph. """
function add!(eg::EGraph, eterm::ETerm)
  eterm = canonicalize!(eg, eterm)
  if haskey(eg.hashcons, eterm)
    eg.hashcons[eterm]
  else
    id = push!(eg.eqrel)
    for argid in children(eterm)
      add_parent!(eg.eclasses[argid], eterm, id)
    end
    eg.hashcons[eterm] = id
    eg.eclasses[id] = EClass(Set([eterm]))
    id
  end
end

find!(eg::EGraph, i::EId) = find_root!(eg.eqrel, i)

function find!(eg::EGraph, e::Expr0) 
  etrm = @match e begin 
    f::Symbol => CallExpr(f)
    Expr(:call, f, xs...) =>  CallExpr(f, find!.(Ref(eg), xs))
    _ => error("Bad Expr $e")
  end
  eid = haskey(eg, etrm) ? eg[etrm] : add!(eg, etrm)
  find_root!(eg, eid)
end

eq(eg::EGraph, x, y) = find!(eg, x) == find!(eg, y)
Base.allequal(eg, xs...) = allequal(find!(Ref(eg), xs))


""" Merge the eclasses associated with two eIDs. """
function Base.merge!(eg::EGraph, id1::EId, id2::EId)
  eg.isclean[] = false
  id1, id2 = find!.(Ref(eg), (id1, id2))
  if id1 == id2
    return id1
  end

  id = union!(eg.eqrel, id1, id2)
  id1, id2 = (id == id1) ? (id2, id1) : (id1, id2)
  push!(eg.worklist, id)
  ec1 = eg.eclasses[id1]
  ec2 = eg.eclasses[id2]
  union!(ec2.reps, ec1.reps)
  merge!(ec2.parents, ec1.parents)
  delete!(eg.eclasses, id1)
  id
end

"""
Reinforces the e-graph invariants (i.e., ensures that the equivalence relation
is congruent).

After modifying an e-graph with `add!` or `merge!`, you must call `rebuild!` to 
restore invariants before any query operations, otherwise the results
may be stale or incorrect.

When the e-graph performs a rebuild operation, it:

- Finds all e-nodes that have become equivalent due to congruence
- Merges their containing e-classes
- Repeats until no more merges are possible

"""
function rebuild!(eg::EGraph)
  """ Rebuild some eclass which has been merged recently """
  function repair!(i::EId)
    # update hashcons of all parent e-terms
    i = find!(eg, i)
    for (p_etrm, p_etrm_class) in eg.eclasses[i].parents
      delete!(eg.hashcons, p_etrm)
      eg.hashcons[canonicalize!(eg, p_etrm)] = find!(eg, p_etrm_class)
    end
  
    new_parents = Parents()
  
    for (p_etrm, p_eclass) in eg.eclasses[i].parents
      p_etrm = canonicalize!(eg, p_etrm)
      if p_etrm ∈ keys(new_parents)
        merge!(eg, p_eclass, new_parents[p_etrm])
      end
      new_parents[p_etrm] = find!(eg, p_eclass)
    end
  
    eg.eclasses[find!(eg, i)].parents = new_parents
  end
  
  while !isempty(eg.worklist)
    todo = [ find!(eg, i) for i in eg.worklist ]
    empty!(eg.worklist)
    repair!.(todo)
  end
  eg.isclean[] = true
end

decompose(s::Symbol) = s => Expr[]

function decompose(s::Expr) 
  s.head == :call || error("Unexpected expr $s")
  s.args[1] => s.args[2:end]
end


####################
# EGraph interface #
####################

""" Naive test backend """
struct NaiveBackend <: EGraphBackend{Expr0, Int} end

init_egraph(::NaiveBackend) = EGraph()

eterm_head(::NaiveBackend, t::ETerm) = t.head

eterm_children(::NaiveBackend, l::ETerm) = l.body

eterm_apply(::NaiveBackend, f::Symbol, children::Vector{EId}) = 
  CallExpr(f, children)

eclass_root(::NaiveBackend, egraph::EGraph, c::EId) = find_root!(egraph, c)

function eterm_lookup(::NaiveBackend, egraph, t::ETerm) 
  egraph.isclean[] || error("Cannot lookup from unclean egraph")
  get(egraph.hashcons, canonicalize!(egraph, t), nothing)
end

function term_lookup(b::NaiveBackend, egraph, t::Expr0) 
  h, args = decompose(t)
  arg_ids = term_lookup.(Ref(b), Ref(egraph), args)
  any(isnothing, arg_ids) && return nothing 
  eterm_lookup(b, egraph, ETerm(h, arg_ids))
end

function eclass_merge(::NaiveBackend, egraph::EGraph, x::EId, y::EId) 
  p = merge!(egraph, x, y)
  rebuild!(egraph)
  p
end

""" 
Boolean return value tells you whether it was actually added (true) vs 
merely being looked up 
"""
function eterm_add(b::NaiveBackend, egraph::EGraph, x::ETerm) 
  egraph.isclean[] || error("Cannot add to unclean egraph")
  has = isnothing(eterm_lookup(b, egraph, x))
  add!(egraph, x) => has
end 

""" 
Boolean return value tells you whether it was actually added (true) vs 
merely being looked up 
"""
function term_add(b::NaiveBackend, egraph::EGraph, x::Expr0) 
  egraph.isclean[] || error("Cannot add to unclean egraph")
  has = isnothing(term_lookup(b, egraph, x))
  add!(egraph, x) => has
end 

eclasses(::NaiveBackend, egraph) = Set(keys(egraph.eclasses))

eterms(::NaiveBackend, egraph, c::EId) = 
  egraph.eclasses[find_root!(egraph, c)].reps

# default to `NaiveBackend` when possible
#----------------------------------------
init_egraph() = init_egraph(NaiveBackend()) # default backend

eclasses(t::EGraph) = eclasses(NaiveBackend(), t) 

eterm_head(t::ETerm) = eterm_head(NaiveBackend(), t) 

eterm_children(l::ETerm) = eterm_children(NaiveBackend(), l)

eterm_apply(f::Symbol, children::Vector{EId}) = 
  eterm_apply(NaiveBackend(), f, children) 

eclass_root(egraph::EGraph, c::EId) = eclass_root(NaiveBackend(), egraph, c)

eterm_lookup(eg::EGraph, t::ETerm) = eterm_lookup(NaiveBackend(), eg, t)

term_lookup(eg::EGraph, t::Expr0) = term_lookup(NaiveBackend(), eg, t)

eclass_merge(eg::EGraph, x::EId, y::EId) = eclass_merge(NaiveBackend(), eg, x, y)

eterm_add(egraph::EGraph, x::ETerm) = eterm_add(NaiveBackend(), egraph, x)

term_add(egraph::EGraph, x::Expr0) = term_add(NaiveBackend(), egraph, x)

eterms(egraph::EGraph, c::EId) = eterms(NaiveBackend(), egraph, c)

end # module
