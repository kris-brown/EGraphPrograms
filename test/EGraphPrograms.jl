module TestEGraphPrograms 

using EGraphPrograms, Test
include("EGraphInterface.jl")
using .TestEGraphInterface

prog = Program()
E = lookup!(prog, :E)
reg = bind!(prog, :typeof, E)
log!(prog, (e=reg,))
ll = interpret!(bk, prog, grph)
@test length(ll) == 3

""" 
Finds a path of length 2 and returns the registers which point to the edges 
"""
function path2(c::Program=Program())
  E = lookup!(c, :E)
  e1 = bind!(c, :typeof, E)
  v = apply!(c, :tgt, e1)
  e2 = bind!(c, :src, v)
  (e1, e2)
end

p2 = Program(); 
log!(p2, NamedTuple(zip([:e1,:e2],path2(p2))))

ex_graph = e_graph_graph([1,1,2],[1,2,2])
log = interpret!(bk, p2, ex_graph)
@test length(log) == 4
merge!(ex_graph, add!.(Ref(ex_graph), [:v1,:v2])...)
rebuild!(ex_graph)
log = interpret!(bk, p2, ex_graph)
@test length(log) == 9 # now only one vertex, so all 3 edges are composable

""" Get a path of length 4 using two `path2` calls. This isn't the most efficient one can do but it's a demonstration of composition of programs """
function path4(c::Program=Program())
  (e1, e2) = path2(c)
  (e3, e4) = path2(c)
  eq!(c, apply!(c, :tgt, e2), apply!(c, :src, e3))
  log!(c, (e1=e1,e2=e2,e3=e3,e4=e4))
  return c
end

res = interpret!(bk, path4(), e_graph_graph([1,2,3,4],[2,3,4,5]))
@test length(res) == 1

end # module