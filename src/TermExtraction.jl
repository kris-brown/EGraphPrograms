module TermExtraction
export extract, eq_terms


using MLStyle
using ..Naive, ..EGraphInterface
using ..Naive: canonicalize!, ETerm
import ..EGraphInterface: extract_term


""" Based on `FasterBottomUpExtractor` """
function extract(eg::EGraph, e_class::EId, weights=nothing)
  e_class = find!(eg, e_class)
  weights = isnothing(weights) ? Dict() : weights
  costs = Dict{EId,Pair{ETerm,Number}}()
  opt() = Dict(k=>v[1] for (k,v) in costs) # throw away the cost number

  # All e-terms and their e-classes
  queue = [canonicalize!(eg, r) => find!(eg, v) 
           for (r,v) in collect(eg.hashcons)]

  costof(t) = get(weights, t.head, 1) + sum(
    [get(costs, find!(eg, arg), nothing=>Inf)[2] for arg in t.body]; init=0)

  while !isempty(queue)
    (eterm, eid) = pop!(queue)
    eid, eterm = find!(eg, eid), canonicalize!(eg, eterm)
    w = costof(eterm)
    if w < get(costs, eid, nothing=>Inf)[2]
      costs[eid] = eterm => w
      # add to queue terms which have changed
      for (parent_term, parent_eid) in eg[eid].parents
        push!(queue, parent_term => parent_eid)
      end
    end
  end
  return make_optimal_term(eg, opt(), e_class)
end

function make_optimal_term(eg::EGraph, opt::Dict, e::Int; seen=Set())
  e′ = find_root!(eg, e)
  etrm = opt[e′]
  e′ ∈ seen && error("Cycle detected: $e′: $etrm")
  push!(seen, e′)
  isempty(etrm.body) && return etrm.head 
  Expr(:call, etrm.head, [make_optimal_term(eg, opt, arg; seen=deepcopy(seen)) 
                          for arg in etrm.body]...)
end


""" All terms in the equivalence class, represented as raw terms """
function eq_terms(eg::EGraph, e::EId) 
  Set(map(collect(eg[find_root!(eg, e)].reps)) do trm
    isempty(trm.body) && return trm.head 
    Expr(:call, trm.head, [extract(eg, arg) for arg in trm.body]...)
  end)
end

eq_terms(eg::EGraph, x) = eq_terms(eg, eg[x])

extract_term(::NaiveBackend, egraph, c::EId) = extract(egraph, c)

end # module
