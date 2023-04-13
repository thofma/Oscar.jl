###
# Tropical hypersurfaces in Oscar
###

################################################################################
#
#  Definition
#
################################################################################

# We use M to record whether we are in the min/max case
# M is either typeof(min) or typeof(max)
# We use EMB to record whether the hypersurface is embedded or abstract
# EMB is either true or false:
#   embedded tropical variety = weighted polyhedral complex in euclidean space
#   abstract tropical variety = weighted hypergraph with enumerated vertices

@attributes mutable struct TropicalHypersurface{M,EMB} <: TropicalVarietySupertype{M,EMB}
    polyhedralComplex::PolyhedralComplex
    function TropicalHypersurface{M,EMB}(Sigma::PolyhedralComplex) where {M,EMB}
        if codim(Sigma)!=1
            error("TropicalHypersurface: input polyhedral complex not one-codimensional")
        end
        return new{M,EMB}(Sigma)
    end
end

function pm_object(T::TropicalHypersurface)
    if has_attribute(T,:polymake_bigobject)
        return get_attribute(T,:polymake_bigobject)
    end
    error("pm_object(T::TropicalHypersurface): Has no polymake bigobject")
end

################################################################################
#
#  Printing
#
################################################################################


function Base.show(io::IO, th::TropicalHypersurface{M, EMB}) where {M, EMB}
    if EMB
        print(io, "$(repr(M)) tropical hypersurface embedded in $(ambient_dim(th))-dimensional Euclidean space")
    else
        print(io, "Abstract $(repr(M)) tropical hypersurface of dimension $(dim(th))")
    end
end

################################################################################
#
#  Constructors for tropical hypersurfaces
#
################################################################################

@doc raw"""
    tropical_hypersurface(f::AbstractAlgebra.Generic.MPoly{Oscar.TropicalSemiringElem{T}})

Return the tropical hypersurface of a tropical polynomial `f`.

# Examples
```jldoctest
julia> T = TropicalSemiring(min)
Tropical semiring (min)

julia> Txy,(x,y) = T["x","y"]
(Multivariate Polynomial Ring in x, y over Tropical semiring (min), AbstractAlgebra.Generic.MPoly{Oscar.TropicalSemiringElem{typeof(min)}}[x, y])

julia> f = x+y+1
x + y + (1)

julia> Tf = tropical_hypersurface(f)
min tropical hypersurface embedded in 2-dimensional Euclidean space
```
"""
function tropical_hypersurface(f::AbstractAlgebra.Generic.MPoly{Oscar.TropicalSemiringElem{T}}) where T
    if total_degree(f) <= 0
        error("Tropical hypersurfaces of constant polynomials not supported.")
    end
    M = convention(base_ring(f))
    fstr = Tuple(tropical_polynomial_to_polymake(f))
    pmpoly = Polymake.common.totropicalpolynomial(fstr...)
    pmhypproj = Polymake.tropical.Hypersurface{M}(POLYNOMIAL=pmpoly)
    pmhyp = Polymake.tropical.affine_chart(pmhypproj)
    Vf = TropicalHypersurface{M, true}(PolyhedralComplex(pmhyp))
    w = Vector{fmpz}(pmhypproj.WEIGHTS)
    set_attribute!(Vf,:polymake_bigobject,pmhypproj)
    set_attribute!(Vf,:tropical_polynomial,f)
    set_attribute!(Vf,:weights,w)
    return Vf
end


@doc raw"""
    tropical_hypersurface(f::MPolyRingElem,M::Union{typeof(min),typeof(max)}=min)

Given a polynomial `f` over a field with an intrinsic valuation (i.e., a field
on which a function `valuation` is defined such as `PadicField(7,2)`),
return the tropical hypersurface of `f` under the convention specified by `M`.

# Examples
```jldoctest
julia> K = PadicField(7, 2);

julia> Kxy, (x,y) = K["x", "y"]
(Multivariate Polynomial Ring in x, y over Field of 7-adic numbers, AbstractAlgebra.Generic.MPoly{padic}[x, y])

julia> f = 7*x+y+49;

julia> tropical_hypersurface(f, min)
min tropical hypersurface embedded in 2-dimensional Euclidean space

julia> tropical_hypersurface(f, max)
max tropical hypersurface embedded in 2-dimensional Euclidean space
```
"""
function tropical_hypersurface(f::MPolyRingElem,M::Union{typeof(min),typeof(max)}=min)
    tropf = tropical_polynomial(f,M)
    Tf = tropical_hypersurface(tropf)
    w = Vector{fmpz}(pm_object(Tf).WEIGHTS)
    set_attribute!(Tf,:algebraic_polynomial,f)
    set_attribute!(Tf,:tropical_polynomial,tropf)
    set_attribute!(Tf,:weights,w)
    return Tf
end

@doc raw"""
    tropical_hypersurface(f::MPolyRingElem,M::Union{typeof(min),typeof(max)}=min)

Construct the tropical hypersurface from a polynomial `f` and a map to the
tropical semiring `val`.

# Examples
```jldoctest
julia> Kx, (x1,x2) = polynomial_ring(QQ,2)
(Multivariate Polynomial Ring in x1, x2 over Rational Field, QQMPolyRingElem[x1, x2])

julia> val = TropicalSemiringMap(QQ,7)
The 7-adic valuation on Rational Field

julia> f = 7*x1+x2+49;

julia> tropical_hypersurface(f, val)
min tropical hypersurface embedded in 2-dimensional Euclidean space
```
"""
function tropical_hypersurface(f::MPolyRingElem, val::TropicalSemiringMap)
    tropf = tropical_polynomial(f,val)
    Tf = tropical_hypersurface(tropf)
    w = Vector{fmpz}(pm_object(Tf).WEIGHTS)
    set_attribute!(Tf,:algebraic_polynomial,f)
    set_attribute!(Tf,:tropical_polynomial,tropf)
    set_attribute!(Tf,:weights,w)
    return Tf
end


################################################################################
#
#  Basic properties for tropical hypersurfaces
#
################################################################################

# todo: add examples for varieties, curves and linear spaces
@doc raw"""
    dual_subdivision(TH::TropicalHypersurface{M, EMB})

Return the dual subdivision of `TH` if it is embedded. Otherwise an error is thrown.

# Examples
A tropical hypersurface in $\mathbb{R}^n$ is always of dimension n-1.
```jldoctest
julia> T = TropicalSemiring(min);

julia> Txy,(x,y) = T["x","y"];

julia> f = x+y+1;

julia> tropicalLine = tropical_hypersurface(f);

julia> dual_subdivision(tropicalLine)
Subdivision of points in ambient dimension 3
```
"""
function dual_subdivision(TH::TropicalHypersurface{M,EMB}) where {M,EMB}
    if !EMB
        error("tropical hypersurface not embedded")
    end

    return SubdivisionOfPoints(pm_object(TH).DUAL_SUBDIVISION)
end


@doc raw"""
    polynomial(TH::TropicalHypersurface{M, EMB})

Return the tropical polynomial of `TH` if it is embedded. Otherwise an error is thrown.

# Examples
```jldoctest
julia> T = TropicalSemiring(min);

julia> Txy,(x,y) = T["x","y"];

julia> f = x+y+1;

julia> TH = tropical_hypersurface(f);

julia> polynomial(TH)
x + y + (1)
```
"""
function polynomial(TH::TropicalHypersurface{M,EMB}) where {M,EMB}
    if !EMB
        error("tropical hypersurface not embedded")
    end
    return get_attribute(TH,:tropical_polynomial)
end


@doc raw"""
    minpoly(T::TropicalHypersurface)

Return the minimal polynomial with smallest possible coefficients of a hypersurface.
"""
function minpoly(T::TropicalHypersurface)
    error("function not implemented yet")
    return
end


###
# Conversion to TropicalVariety
###
@doc raw"""
    tropical_variety(Tf::TropicalHypersurface)

Converts a `TropicalHypersurface` to a `TropicalVariety`.

# Examples
```jldoctest
julia> T = TropicalSemiring(min);

julia> Txy,(x,y) = T["x","y"];

julia> f = x+y+1;

julia> TH = tropical_hypersurface(f);

julia> TV = tropical_variety(TH)
min tropical variety of dimension 1 embedded in 2-dimensional Euclidean space
```
"""
function tropical_variety(Tf::TropicalHypersurface)
    TV = TropicalVariety{convention(Tf),is_embedded(Tf)}(Tf.polyhedralComplex)
    set_attribute!(TV,:weights,weights(Tf))
    return TV
end
