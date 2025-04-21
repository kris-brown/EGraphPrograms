module EGraphPrograms
using Reexport 


include("EGraphInterface.jl")
@reexport using .EGraphInterface

include("Programs.jl")
@reexport using .Programs

include("ProgramOptimization.jl")
@reexport using .ProgramOptimization

include("Naive.jl")
@reexport using .Naive

include("TermExtraction.jl")
@reexport using .TermExtraction

# Methods that are defined in package extensions
export theory_programs, to_e_graph, saturate!, validate

function theory_programs end
function to_e_graph end 
function saturate! end
function validate end

end # module
