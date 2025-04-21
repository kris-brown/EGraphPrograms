module TestEGraphInterface

export bk, e_graph_graph, grph

using EGraphPrograms, Test

bk = NaiveBackend()

""" 
Make an egraph with `src`/`tgt`/`typeof` unary functions representing a 
directed multigraph.
"""
function e_graph_graph(src::Vector{Int}, tgt::Vector{Int}, nV=nothing)
  length(src) == length(tgt) || error("src/tgt maps must be equal length")
  nV = maximum([src; tgt; (isnothing(nV) ? 0 : nV)])
  nE = length(src)

  # Generators
  vs = [Symbol("v$i") for i in 1:nV]
  es = [Symbol("e$i") for i in 1:nE]

  # Equivalent terms 
  ety = [[Expr(:call, :typeof, e) for e in es]..., :E]
  vty = [[Expr(:call, :typeof, v) for v in vs]..., :V]
  srcs = [[vs[i], [Expr(:call, :src, es[p]) for p in findall(==(i), src)]...]   
          for i in 1:nV]
  tgts = [[vs[i], [Expr(:call, :tgt, es[p]) for p in findall(==(i), tgt)]...] 
          for i in 1:nV]
  equivalent_terms = [ety, vty, srcs..., tgts...]
  add_egraph_data!(bk, EGraph(), equivalent_terms)
end

# ↻•→•↺
grph = e_graph_graph([1,1,2],[1,2,2]);

# All the edges are of type :E
@test eq_terms(grph, grph[:E]) == Set([
  :E, :(typeof(e1)), :(typeof(e2)), :(typeof(e3))
])

# We can refer to a vertex directly or as an expression.
@test extract(grph, add!(grph, :(src(e1)))) == :v1
@test extract(grph, add!(grph, :(tgt(e3)))) == :v2


end  # module
