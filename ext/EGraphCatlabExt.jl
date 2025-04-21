module EGraphCatlabExt 

using Catlab, EGraphPrograms
import Catlab.Graphics: Graphviz
using EGraphPrograms.Naive: ETerm, decompose


const colors = ["yellow", "pink", "lightblue", "green"]

"""
Visualize an e-graph as a DWD.

Optionally pass in a vector of terms which will be highlighted in the diagram.
"""
function Catlab.to_graphviz(eg::EGraph, terms=[])
  n(i::Int) = fill(nothing, i)
  termcolors = Dict()
  terms′ = Dict(map(zip(terms,colors)) do (x,color) 
    h, args = decompose(x)
    ETerm(h, term_lookup.(Ref(eg), args)) => color
  end)
  wd = WiringDiagram([],[])
  eclass_ids = sort(collect(keys(eg.eclasses)))
  eclass_dic = Dict(v=>k for (k,v) in enumerate(eclass_ids))
  for _ in 1:nclasses(eg)
    add_box!(wd, Junction(nothing, n(1), n(1)))
  end
  for (t, c) in pairs(eg.hashcons)
    b = add_box!(wd, Box(t.head, n(length(t)), n(1)))
    termcolors[b] = get(terms′, t, "white")
    for (i, k) in enumerate(t.body)
      add_wire!(wd, (eclass_dic[find!(eg, k)], 1)=>(b, i))
    end
    add_wire!(wd, ((b, 1)=>(eclass_dic[find!(eg, c)], 1)))
  end
  G = to_graphviz(wd; orientation=LeftToRight)
  for (b, color) in pairs(termcolors)
    stmt = G.stmts[b]
    G.stmts[b] = Graphviz.Node(stmt.name, merge(stmt.attrs, Dict(:fillcolor=>color, :style=>"filled")))
  end
  G
end


end # module
