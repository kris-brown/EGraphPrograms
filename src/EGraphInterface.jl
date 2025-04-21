module EGraphInterface
export EGraphBackend, init_egraph, eterm_head,eterm_children, eterm_apply, 
       extract_term, eclass_root, eterms, term_lookup, eterm_lookup, 
       eclass_merge, eterm_add, term_add,  eclasses,
       add_egraph_data!
using MLStyle


# E-Graph Primitives
###################
"""
An `EGraphBackend` controls dispatch to control which implementation of the 
following methods gets used. These are generic E Graph instructions which could 
be interpreted by any backend.
"""
abstract type EGraphBackend{AbsETerm, AbsEClass} end 

""" initialize an egraph """
function init_egraph end

""" Head of an e-term (paradigm case: a symbol) """
function eterm_head end  

""" Children of e-term: returns a vector of e-classes """
function eterm_children end 

# Construct an eterm given a head and a list of child e-class IDs
function eterm_apply end 

# Extract a (good) raw term from the e-class `c`
function extract_term end

# Get root e-class of an e-class
function eclass_root end

# Iterator for the canonical eclasses
function eclasses end 

# Iterator for the e-terms with e-class `c`
function eterms end 

# Get e-class id from an e-term `x`  (if exists, else return `nothing`)
function eterm_lookup end

# Get e-class id from an e-term `x`  (if exists, else return `nothing`)
function term_lookup end

# Merge two e-class ids. Return the parent.
function eclass_merge end

# Add new (raw) term to the graph. Return corresponding e-class ID and a 
# boolean which indicates whether the e-graph changed
function term_add end

# Add an eterm to the graph. Return corresponding e-class ID and a 
# boolean which indicates whether the e-graph changed
function eterm_add end

""" 
Initialize an egraph via a list of lists, where each sublist is a list of 
terms (which will be added to the egraph) and being in the same sublist 
implicitly represents that these terms should be equated.
""" 
function add_egraph_data!(b::EGraphBackend, eg, eqs)
  for eqlist in eqs 
    classlist = unique(first.(term_add.(Ref(b), Ref(eg), eqlist)))
    for (c1, c2) in zip(classlist, classlist[2:end])
      eclass_merge(b, eg, c1, c2)
    end
  end
  return eg
end


end # module
