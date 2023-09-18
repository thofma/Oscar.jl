# avoid polluting the main namespace to to preserve proper printing in doctests
module SLPTest
using ..Test
using ..Oscar
const SLP = Oscar.StraightLinePrograms

# make sure to use the custom include function to collect stats
include(str::String) = Main.include(str, SLPTest)

include("setup.jl")
include("straightline.jl")
include("gap.jl")
include("atlas.jl")

end
