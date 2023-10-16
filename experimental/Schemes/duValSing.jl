@doc raw"""
    has_du_val_singularities(X::Scheme)

Return whether the given ``X`` has at most du Val (surface) singularities.

# Example:
```jldoctest
julia> R,(x,y,z,w) = QQ["x","y","z","w"]
(Multivariate polynomial ring in 4 variables over QQ, QQMPolyRingElem[x, y, z, w])

julia> I = ideal(R,[w,x^2+y^3+z^4])
ideal(w, x^2 + y^3 + z^4)

julia> Rq,_ = quo(R,I)
(Quotient of multivariate polynomial ring by ideal(w, x^2 + y^3 + z^4), Map: multivariate polynomial ring -> quotient of multivariate polynomial ring)

julia> X = Spec(Rq)
Spectrum
  of quotient
    of multivariate polynomial ring in 4 variables x, y, z, w
      over rational field
    by ideal(w, x^2 + y^3 + z^4)

julia> has_du_val_singularities(X)
true

```
"""
function has_du_val_singularities(X::AbsProjectiveScheme{<:Field,<:Any})
  return has_du_val_singularities(covered_scheme(X))
end

function has_du_val_singularities(X::AbsSpec{<:Field,<:Any})
  R = OO(X)
  I = modulus(R)
  
  J = image_ideal(singular_locus(X)[2])
  J = ideal(base_ring(I), lift.(gens(J))) + I
  dim(J) == 0 || return false                            ## non-isolated
  return is_du_val_singularity(X,J)
end

function has_du_val_singularities(X::AbsCoveredScheme{<:Field})
  C = (has_attribute(X, :simplified_covering) ? simplified_covering(X) : default_covering(X))

  I = ideal_sheaf_of_singular_locus(X)
  decomp = maximal_associated_points(I)

  ## we do the double loop here to avoid unnecessary checks
  for J in decomp
    for U in C
      !isone(J(U)) || continue
      is_du_val_singularity(U,saturated_ideal(J(U))) || return false    ## testing the point in one chart suffices
      break
    end
  end

  return true
end

@doc raw"""
    is_du_val_singularity(X::AbsSpec, I::Ideal)

Return whether the given ``X`` has at most du Val (surface) singularities at the geometric points specified by the ideal ``I``.

**Note**: For the ideal ``I`` in a ring ``R``, `dim(R/I) = 0` is asserted

# Example:
```jldoctest
julia> R,(x,y,z,w) = QQ["x","y","z","w"]
(Multivariate polynomial ring in 4 variables over QQ, QQMPolyRingElem[x, y, z, w])

julia> I = ideal(R,[w,x^2+y^3+z^4])
ideal(w, x^2 + y^3 + z^4)

julia> Rq,_ = quo(R,I)
(Quotient of multivariate polynomial ring by ideal(w, x^2 + y^3 + z^4), Map: multivariate polynomial ring -> quotient of multivariate polynomial ring)

julia> J = ideal(R,[x,y,z,w])
ideal(x, y, z, w)

julia> X = Spec(Rq)
Spectrum
  of quotient
    of multivariate polynomial ring in 4 variables x, y, z, w
      over rational field
    by ideal(w, x^2 + y^3 + z^4)

julia> is_du_val_singularity(X,J)
true

```
"""
function is_du_val_singularity(X::AbsSpec{<:Field,<:Any},I::Ideal)
  OOX = OO(X)
  dim(X) == 2 || error("Scheme not of dimension 2")
  J = modulus(OOX)
  !isone(J) || error("Scheme is empty")
  !iszero(J) || return true                  ## X smooth

  R = base_ring(I)
  kk = base_ring(R)
  characteristic(kk) == 0 || characteristic(kk) > 7 || error("not available in small characteristic")
  base_ring(OOX) === R || error("base rings need to be identical")

  dim(I) == 0 || error("second argument does not describe a 0-dimensional scheme")
  if get_attribute(I,:is_absolutely_prime, false)
    return _check_duval_at_point(J,I)[1]
  end

  decomp = absolute_primary_decomposition(I)

  for (_,_,I2,mult) in decomp
    set_attribute!(I2,:is_absolutely_prime,true)
    ## pass to algebraic extension
    r_changed = base_ring(I2)
    kk = coefficient_ring(r_changed)
    J_changed = ideal(r_changed,  [change_coefficient_ring(kk,a, parent = r_changed) for a=gens(J)])
    is_du_val_singularity(Spec(quo(r_changed,J_changed)[1]),I2) || return false
  end
  
  return true
end

@doc raw"""
    decide_du_val_singularity(X::AbsSpec, I::Ideal)

Return a vector of tuples ``T`` with the following data:
- `T[1]::Bool` answers whether ``X`` has at most du Val (surface) singularities at the geometric points specified by the ideal ``I``.
- `T[2]::Ideal` is ``I_P`` the associated prime of `I` (possibly over a suitable field extension) describing some geometrically irreducible point
- `T[3]::Tuple` contains the type of the singularity at ``P``  e.g. `(:A, 3)`
- `T[4]::Int` number of conjugate points

If ``X`` has a least one singularity which is not du Val, the returned vector contains a single tuple ``T``, with the following values:
- `T[1]`  is `false`
- `T[2]` represents a point at which some non-du-Val singularity is present
- `T[3]` is the empty tuple
- `T[4] = 1`

**Note**: For the ideal ``I`` in a ring ``R``, `dim(R/I) = 0` is asserted

# Example:
```jldoctest
julia> R,(x,y,z,w) = QQ["x","y","z","w"]
(Multivariate polynomial ring in 4 variables over QQ, QQMPolyRingElem[x, y, z, w])

julia> I = ideal(R,[w,x^2+y^3+z^4])
ideal(w, x^2 + y^3 + z^4)

julia> Rq,_ = quo(R,I)
(Quotient of multivariate polynomial ring by ideal(w, x^2 + y^3 + z^4), Map: multivariate polynomial ring -> quotient of multivariate polynomial ring)

julia> J = ideal(R,[x,y,z,w])
ideal(x, y, z, w)

julia> X = Spec(Rq)
Spectrum
  of quotient
    of multivariate polynomial ring in 4 variables x, y, z, w
      over rational field
    by ideal(w, x^2 + y^3 + z^4)

julia> decide_du_val_singularity(X,J)
1-element Vector{Any}:
 (true, ideal(w, z, y, x), (:E, 6), 1)
```
""" 
function decide_du_val_singularity(X::AbsSpec{<:Field,<:Any},I::MPolyIdeal)
  OOX = OO(X)
  dim(X) == 2 || error("Scheme not of dimension 2")
  J = modulus(OOX)
  !isone(J) || error("Scheme is empty")
  !iszero(J) || return true                  ## X smooth

  R = base_ring(I)
  kk = base_ring(R)
  characteristic(kk) == 0 || error("only available in characteristic zero")
  base_ring(OOX) === R || error("base rings need to be identical")

  dim(I) == 0 || error("second argument is not a point")
  if get_attribute(I,:is_absolutely_prime, false)
    li = _check_duval_at_point(J,I)
    return [(li[1], I, li[2],1)]
  end

  result_vector = []
  decomp = absolute_primary_decomposition(I)
  for (_,_,I2,mult) in decomp
    set_attribute!(I2,:is_absolutely_prime,true)
    ## pass to algebraic extension
    r_changed = base_ring(I2)
    kk = coefficient_ring(r_changed)
    J_changed = ideal(r_changed,  [change_coefficient_ring(kk,a, parent = r_changed) for a=gens(J)])
    tempvec = decide_du_val_singularity(Spec(quo(r_changed,J_changed)[1]),I2)
    for x in tempvec
      x[1] || return [x]
      x = (x[1],x[2],x[3],mult)
      push!(result_vector,x)
    end
  end

  return result_vector
end

@doc raw"""
    _check_du_val_at_point(IX:Ideal,Ipt::Ideal)

Returns a tuple `T` with the following data:
- `T[1]::Bool` returns whether `V(IX)` has at most a du Val singularity at `V(Ipt)`
- `T[2]::Tuple` Type of du Val singularity at `V(Ipt)`

**Note**: Assumes ``Ipt`` to be absolutely irreducible.

**Note**: Do not call directly, only via the higher level functions is_du_Val_singularity and decide_du_Val_singularity.

"""
function _check_duval_at_point(IX::Ideal,Ipt::Ideal)
  R = base_ring(IX)
  R == base_ring(Ipt) || error("basering mismatch")
  kk = base_ring(R)
  characteristic(kk) == 0 || error("only available in characteristic zero")
 
  JM = jacobi_matrix(gens(IX))

  smooth = (:A,0)

  ## localize at point
  a = rational_point_coordinates(Ipt)
  U = complement_of_point_ideal(R,a)
  RL, loc_map = localization(R,U)
  IX_loc = loc_map(IX)
  JM_loc =  map(x ->loc_map(x), JM[:,:])

  if !all(iszero(a))
    F_loc = free_module(RL,ngens(IX))
    Jm = sub(F_loc,JM_loc)[1]
    Jm = Jm + (loc_map(IX)*F_loc)[1]
    Jm_shifted = shifted_module(Jm)[1]
    F_shifted = ambient_free_module(Jm_shifted)
  else
    F = free_module(R,ngens(IX))
    Jm = sub(F,JM)[1]
    Jm_shifted = Jm + (IX * F)[1]
    F_shifted = F
  end

  o = negdegrevlex(R)*lex(F_shifted)
  F1 = leading_module(Jm_shifted,o)
  F1quo = quo(F_shifted, F1)[1]

  constant_mons = vector_space_dimension(F1quo,0) 
  constant_mons < 2 || return (false, typeof(smooth))                   ## not a hypersurface
  constant_mons > 0 || return (true, smooth)                            ## no singularity
  
  tau = vector_space_dimension(F1quo)

  corank = vector_space_dimension(F1quo,1)
  corank < 3 || return (false,typeof(smooth))                           ## at least T_3,3,3 not duVal
  corank > 1 || return (true,(:A,tau))                                  ## A_series

  # we now already know essentially a hypersurface of corank 2, count degrees of freedom cubicpart
  cubiccount = vector_space_dimension(F1quo,2)
  cubiccount < 3 || return  (false, typof(smooth))                      ## at least X_9
  cubiccount > 1 || return  (true, (:D,tau))                            ## D_series

  # it is definitely in the E/J series
  tau < 9 || return(false, typeof(smooth))                              ## at least J_10
  return (true, (:E,tau))                                               ## E_6, E_7, E_8
end

