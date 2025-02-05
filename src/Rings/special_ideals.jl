function _get_katsura_exponent(n::Int, m::Int, l::Int)
    e = zeros(Int, n + 1)
    if abs(l) == abs(m - l)
        e[abs(l) + 1] = 2
    else
        e[abs(l) + 1] = 1
        e[abs(m - l) + 1] = 1
    end

    return e
end

@doc raw"""
    katsura(n::Int)

Given a natural number `n` return the Katsura ideal over the rational numbers generated by
$u_m - \sum_{l=-n}^n u_{l-m} u_l$, $1 - \sum_{l = -n}^n u_l$
where $u_{-i} = u_i$, and $u_i = 0$ for $i > n$ and $m \in \{-n, \ldots, n\}$.

Note that indices have been shifted to start from 1.

# Examples
```jldoctest
julia> I = katsura(2)
ideal(x1 + 2*x2 + 2*x3 - 1, x1^2 - x1 + 2*x2^2 + 2*x3^2, 2*x1*x2 + 2*x2*x3 - x2)
julia> base_ring(I)
Multivariate polynomial ring in 3 variables x1, x2, x3
  over rational field
```
"""
function katsura(n::Int)
    R, _ = polynomial_ring(QQ, n + 1)
    return katsura(R)
end

@doc raw"""
    katsura(R::MPolyRing)

Return the Katsura ideal in the given polynomial ring `R`.

# Examples
```jldoctest
julia> R, _ = QQ["x", "y", "z"]
(Multivariate polynomial ring in 3 variables over QQ, QQMPolyRingElem[x, y, z])

julia> katsura(R)
ideal(x + 2*y + 2*z - 1, x^2 - x + 2*y^2 + 2*z^2, 2*x*y + 2*y*z - y)
```
"""
function katsura(R::MPolyRing)
    CR = coefficient_ring(R)
    polys = elem_type(R)[]
    n = nvars(R) - 1
    coeffs_vec = 2 * ones(elem_type(CR), n + 1)
    coeffs_vec[1] = CR(1)
    mono_exps = Matrix{Int}(identity_matrix(ZZ, n + 1))
    linear_poly = R(coeffs_vec, [mono_exps[:, i] for i in 1:ncols(mono_exps)])
    linear_poly -= R(1)
    push!(polys, linear_poly)
    
    for m in 0:n - 1
        polynomial = MPolyBuildCtx(R)
        for l in -n:n
            if abs(l) > n || abs(m - l) > n 
                continue
            end
            e = _get_katsura_exponent(n, m, l)
            push_term!(polynomial, CR(1), e)
        end

        e = zeros(Int, n + 1)
        e[abs(m) + 1] = 1
        push_term!(polynomial, CR(-1), e)
        poly = finish(polynomial)
        push!(polys, poly)
    end

    return ideal(R, polys)
end
