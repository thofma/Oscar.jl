using Test

include("AffineSchemes.jl")
include("AffineVariety.jl")
include("AffineAlgebraicSet.jl")
include("CartierDivisor.jl")
include("CoveredProjectiveSchemes.jl")
include("CoveredScheme.jl")
include("CoherentSheaves.jl")

# disabled on 1.10 and nightly due to #2441
# moved to main runtests.jl for conditional testing
#include("elliptic_surface.jl")

include("FunctionFields.jl")
include("Glueing.jl")
include("IdealSheaves.jl")
include("K3.jl")
include("ProjectiveAlgebraicSet.jl")
include("ProjectiveSchemes.jl")
include("ProjectiveVarieties.jl")
include("Sheaves.jl")
include("SpaceGerms.jl")
include("SpecOpen.jl")
include("SpecialTypes.jl")
include("singular_locus.jl")
include("SimplifiedSpec.jl")
include("transforms.jl")
include("VectorBundles.jl")
include("WeilDivisor.jl")
include("duValSing.jl")
include("RationalMap.jl")

