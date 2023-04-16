# dummy has to fix https://github.com/oscar-system/Oscar.jl/issues/2222
Base.hash(::Polyhedron, h::UInt) = h ^ 0x1234567

# takes a matrix over QQ,
# multiplies each row by the lcm of their denominators,
# returns a matrix over ZZ.
function primitive(M::fmpq_mat)
    N = fmpz_mat(nrows(M),ncols(M))
    for i in 1:nrows(M)
        N[i,:] = numerator.(M[i,:]*lcm(denominator.(M[i,:])))
    end
    return N
end

# Input: B1, B2 matrices whose rows are generating sets of two euclidean linear spaces,
#               whose sum is the entire space
# Output: the tropical intersection number as defined in [Maclagan-Sturmfels, Definition 3.6.5]
function tropical_intersection_multiplicity(B1::fmpq_mat,B2::fmpq_mat)
    @assert ncols(B1) == ncols(B2) && nrows(B1)+nrows(B2) >= ncols(B1)

    # primitive scales every row by the lcm of the denominators, making the matrix integral
    # saturate computes a basis of the saturation of the sublattice spanned by the row vectors
    B1 = saturate(primitive(B1))
    B2 = saturate(primitive(B2))

    snfB12 = snf(vcat(B1,B2))
    return abs(prod([snfB12[i,i] for i in 1:ncols(snfB12)]))
end

# Given two polyhedra intersecting each other,
# returns the tropical intersection multiplicity
function tropical_intersection_multiplicity(sigma1::Polyhedron, sigma2::Polyhedron)
    B1 = affine_equation_matrix(affine_hull(sigma1))
    B2 = affine_equation_matrix(affine_hull(sigma2))
    return tropical_intersection_multiplicity(B1[:,2:end],B2[:,2:end])
end

function unique_point(P::Polyhedron)

    # compute sum of vertices and ray generators modulo lineality space
    R,_ = rays_modulo_lineality(P)
    V,_ = minimal_faces(P)
    pt = sum(vcat(R,V))
    # return primitive integer vector
    return numerator.(pt .* lcm(denominator.(pt)))

end

function get_weight(weights::Dict{Vector{fmpz},fmpz},sigma)
    weight = get(weights,unique_point(sigma),-1)
    @assert weight>0
    return weight
end


function polyhedral_complex_from_polyhedra(listOfPolyhedra::Vector{<: Polyhedron})

    ###
    # Collect incidence information of rays and vertices
    ###
    raysList = Vector{Vector{fmpq}}() # list of rays
    vertsList = Vector{Vector{fmpq}}() # list of vertices
    incidencesRays = Vector{Vector{Int}}() # list of ray incidences
    incidencesVerts = Vector{Vector{Int}}() # list of vertex incidences

    for sigma in listOfPolyhedra
        incidenceRays = Vector{Int}() # new ray incidence vector of sigma
        for ray in rays(sigma)
            i = findfirst(isequal(ray),raysList)
            # if ray does not occur in rays, add it
            # either way add the corresponding index to incidenceRays
            if i === nothing
                push!(raysList,ray)
                push!(incidenceRays,length(raysList))
            else
                push!(incidenceRays,i)
            end
        end
        push!(incidencesRays,incidenceRays)

        incidenceVerts = Vector{Int}() # new vertex incidence vector of sigma
        for vert in vertices(sigma)
            i = findfirst(isequal(vert),vertsList)
            # if vert does not occur in verts, add it
            # either way add the corresponding index to incidenceVerts
            if i === nothing
                push!(vertsList,vert)
                push!(incidenceVerts,length(vertsList))
            else
                push!(incidenceVerts,i)
            end
        end
        push!(incidencesVerts,incidenceVerts)
    end

    ###
    # Merge incidence information of rays and vertices and convert to the right type
    ###
    incidences = [vcat(irays,iverts) for (irays,iverts) in zip(incidencesRays,incidencesVerts)]
    raysAndVerts = vcat(raysList,vertsList)
    incidences = IncidenceMatrix(incidences) # convert Vector{Vector} to IncidenceMatrix
    raysAndVerts = matrix(QQ,raysAndVerts)   # convert Vector{Vector} to Matrix

    # construct lineality space
    sigma = first(listOfPolyhedra)
    linealitySpace = lineality_space(sigma)


    return PolyhedralComplex(incidences,
                             raysAndVerts,
                             collect(1:length(raysList)),
                             linealitySpace)
end


import Base.isempty
function isempty(P::Polyhedron)
    return dim(P)<0
end


# returns true if sigma1 intersects (eps*direction + sigma2) for eps>0 sufficiently small
# returns false otherwise
function intersects_after_perturbation(sigma1::Polyhedron, sigma2::Polyhedron, direction::Vector{fmpz})

    ###
    # Quick test, do sigma1 and sigma2 even intersect
    ###
    if isempty(intersect(sigma1,sigma2))
        return false
    end

    ###
    # Construct  sigma1 x RR  in RR^{n+1}
    ###
    # read off inequalities and equations of sigma1
    ineqs1 = affine_inequality_matrix(facets(sigma1))
    ineqs1Matrix = ineqs1[:,2:end]
    ineqs1Vector = [-ineqs1[i,1] for i in 1:nrows(ineqs1)]
    eqs1 = affine_equation_matrix(affine_hull(sigma1))
    eqs1Matrix = eqs1[:,2:end]
    eqs1Vector = [-eqs1[i,1] for i in 1:nrows(eqs1)]
    # append 0 column to the matrices to construct sigma1 x RR
    ineqs1Matrix = hcat(ineqs1Matrix,fmpq_mat(nrows(ineqs1Matrix),1))
    eqs1Matrix = hcat(eqs1Matrix,fmpq_mat(nrows(eqs1Matrix),1))
    sigma1Lifted = Polyhedron((ineqs1Matrix,ineqs1Vector),(eqs1Matrix,eqs1Vector))

    ###
    # Construct  ( sigma2 x {0} ) + ( direction x {1} )  in RR^{n+1}
    ###
    # read of vertices, rays, and lineality of sigma2
    V,_ = minimal_faces(sigma2)
    R,L = rays_modulo_lineality(sigma2)
    R,V,L = matrix.(Ref(QQ),[R,V,L])

    # append 0 column to embed them into RR^{n+1} to construct sigma2 x {0}
    V = hcat(V,fmpq_mat(nrows(V),1))
    R = hcat(R,fmpq_mat(nrows(R),1))
    L = hcat(L,fmpq_mat(nrows(L),1))

    # append 1 to direction to construct direction x {1} and add it to rays
    directionLifted = deepcopy(direction) # making sure input direction does not get overwritten
    push!(directionLifted,1)
    R = vcat(R,matrix(QQ,[directionLifted]))
    sigma2Lifted = convex_hull(V,R,L)


    ###
    # Compute their intersection and check whether it is more than {0}.
    # If it is, compute a relative interior point
    # and check whether the last coordinate is positive
    ###
    sigma12 = intersect(sigma1Lifted,sigma2Lifted)
    if dim(sigma12)<1
        return false
    end
    pt = relative_interior_point(sigma12)
    return last(pt)>0

end


@doc raw"""
    intersect_stably(T1::TropicalVariety,T2::TropicalVariety)

Given two tropical varieties `T1` and `T2`, i.e., two balanced polyhedral complexes, returns their stable intersection.

# Examples
```jldoctest
julia> Txy,(x,y) = TropicalSemiring()["x","y"];

julia> f1 = x+y+0;

julia> f2 = 1*x^2+x*y+1*y^2+x+y+1;

julia> T1 = tropical_variety(tropical_hypersurface(f1)); # standard tropical line

julia> T2 = tropical_variety(tropical_hypersurface(f2)); # honeycomb quadric

julia> T12 = intersect_stably(T1, T2) # one point of weight 2
min tropical variety of dimension 0 embedded in 2-dimensional Euclidean space

julia> display(vertices(T12))
1-element SubObjectIterator{PointVector{QQFieldElem}}:
 [0, 0]

julia> display(weights(T12))
Dict{Vector{ZZRingElem}, ZZRingElem} with 1 entry:
  [0, 0] => 2

julia> T22 = intersect_stably(T2, T2) # four points of weight 1
min tropical variety of dimension 0 embedded in 2-dimensional Euclidean space

julia> display(vertices(T22))
4-element SubObjectIterator{PointVector{QQFieldElem}}:
 [-1, 0]
 [1, 1]
 [0, -1]
 [0, 0]

julia> display(weights(T22))
Dict{Vector{ZZRingElem}, ZZRingElem} with 4 entries:
  [1, 1]  => 1
  [0, 0]  => 1
  [-1, 0] => 1
  [0, -1] => 1

```
"""
function intersect_stably(T1::TropicalVariety, T2::TropicalVariety;
                          perturbation::Vector{fmpz}=fmpz[])

    # Pick a random perturbation if not passed
    # and initialise a list of polyhedra and weight dictionary
    if isempty(perturbation)
        perturbation = fmpz.(rand(Int,ambient_dim(T1)))
    end
    T12 = Polyhedron[]
    weights12 = Dict{Vector{fmpz},fmpz}()

    # Loop over all maximal polyhedra of T1 and T2 (and their weights) such that
    weights1 = weights(T1)
    weights2 = weights(T2)
    for sigma1 in maximal_polyhedra(T1)
        m1 = get_weight(weights1,sigma1)
        for sigma2 in maximal_polyhedra(T2)
            m2 = get_weight(weights2,sigma2)

            # (a) their minkowski sum is full-dimensional
            if !isfulldimensional(sigma1 + sigma2)
                continue
            end

            # (b) they intersected after perturbation
            if !intersects_after_perturbation(sigma1,sigma2,perturbation)
                continue
            end

            # compute their intersection, the unique identifying point thereof
            # and the tropical intersection multiplicity
            sigma12 = intersect(sigma1, sigma2)
            p12 = unique_point(sigma12)
            m12 = m1*m2*tropical_intersection_multiplicity(sigma1,sigma2)

            # add m12 to the weight dictionary
            if haskey(weights12,p12)
                weights12[p12] += m12
            else
                get!(weights12,p12,m12)
                push!(T12,sigma12)
            end
        end
    end

    # Assemble and return tropical variety
    T12 = polyhedral_complex_from_polyhedra(T12)
    T12 = TropicalVariety{convention(T1),is_embedded(T1)}(T12)
    set_attribute!(T12,:weights,weights12)
    return T12
end
