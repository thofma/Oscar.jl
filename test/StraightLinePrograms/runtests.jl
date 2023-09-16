# avoid polluting the main namespace to to preserve proper printing in doctests
module SLPTest
using ..Test
using ..Oscar
const SLP = Oscar.StraightLinePrograms

# make sure to use the custom include function to collect stats
Main.include("setup.jl")
Main.include("straightline.jl")
Main.include("gap.jl")
Main.include("atlas.jl")

end
