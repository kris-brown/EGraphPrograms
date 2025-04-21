# EGraphPrograms
Experimental e-graph library




## EGraph Interface

This library defines an interface for E-Graphs in `EGraphInterface.jl`.
```julia 
# initialize an egraph
function init_egraph end

# Head of an e-term (paradigm case: a symbol)
function eterm_head end  

# Children of e-term: returns a vector of e-classes
function eterm_children end 

# Construct an eterm given a head and a list of child e-class IDs
function eterm_apply end 

# Extract a (good) raw term from an e-class
function extract_term end

# Get root e-class of an e-class
function eclass_root end

# Iterator for the canonical eclasses
function eclasses end 

# Iterator for the e-terms with some particular e-class 
function eterms end 

# Get e-class id from an e-term (if exists, else return `nothing`)
function eterm_lookup end

# Get e-class id from an e-term (if exists, else return `nothing`)
function term_lookup end

# Merge two e-class ids. Return the parent.
function eclass_merge end

# Add new (raw) term to the graph. Return corresponding e-class ID and a 
# boolean which indicates whether the e-graph changed
function term_add end

# Add an eterm to the graph. Return corresponding e-class ID and a 
# boolean which indicates whether the e-graph changed
function eterm_add end
```

## Naive implementation 
This library provides a particular implementation of the above interface in in `Naive.jl`. It has the following data structure for e-terms:

```julia 
@struct_hash_equal struct CallExpr
  head::Symbol
  body::Vector{EId}
  CallExpr(f::Symbol, body=EId[]) = new(f, body)
end
```

where `EId` is a synonym for `Int`.

The data structure for an e-graph is the following:

```julia 
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
```

## Programs 

A language for high-level programs is found in `EGraphPrograms.jl`. These programs are interpreted in the context of a register of memory which is a vector of e-class IDs. As the program progresses, it fills out more and more of the vector. Backtracking is easy because we simply jump back to an earlier register,

```julia 
@data EGraphProgramInstruction begin

  # Lookup (or add) raw term `x` and store its e-class ID in the register `reg`
  Lookup!(x, reg::Reg)

  # Iterate over {eclass(x) | f(x) ≅ y ∧ g(x) ≅ z ∧ ... } 
  # and store e-class ids in register `reg`. `d` stores pairs `f=>y` etc.
  Bind!(d::Dict{Symbol, Reg}, reg::Reg)

  # get eclass id associated with `f(x₁,x₂,...)`, store in register `reg` (if it exists, else quit)
  Apply!(f::Symbol, xs::Vector{Reg}, reg::Reg)

  # get eclass id associated with `f(x₁,x₂,...)`, store in register `reg` (create if not exists)
  Insert!(f::Symbol, xs::Vector{Reg}, reg::Reg)

  # Assert that two registers have equal values
  Guard!(r1::Reg, r2::Reg)
  
  # Assert that two registers have distinct values
  AntiGuard!(r1::Reg, r2::Reg)

  # For debug purposes
  Print!(reg::Reg, msg::String)

  # Output a namedtuple of register values
  Log!(regs::NamedTuple)

  # Merge the eclasses associated with two registers
  Merge!(r1::Reg, r2::Reg)

end 
```

