using Oscar

export get_stratum_smooth_curve


@doc raw"""
    get_stratum_smooth_curve(f::MPolyRingElem, k::Int)

Given a homogeneous polynomial f in 3 variables defining a smooth plane curve,
output polynomials defining the locus where the hyperplane c\_1*x + c\_2*y + c\_3*z intersects V(f) in deg(f)-k many points.

## Example 

```jldoctest
julia> R, (x,y,z) = polynomial_ring(QQ, ["x","y","z"])
(Multivariate polynomial ring in 3 variables over QQ, QQMPolyRingElem[x, y, z])

julia> f = x^3 - x*z^2 - y^2*z + z^3
x^3 - x*z^2 - y^2*z + z^3

julia> I = ideal(get_stratum_smooth_curve(f, 2))
Ideal generated by
  z0^4*z1 + 36*z0^3*z1*z2 + 36*z0^2*z1^3 + 30*z0^2*z1*z2^2 + 48*z0*z1^3*z2 - 69*z1^5 + 108*z1^3*z2^2 - 27*z1*z
  2^4
  6*z0^5 + 5*z0^4*z2 + z0^3*z1^2 + 27*z0^2*z1^2*z2 - 3*z0^2*z2^3 + 9*z0*z1^4 + 15*z0*z1^2*z2^2 + 6*z1^4*z2
  -5*z0^4*z2 + 53*z0^3*z1^2 - 18*z0^3*z2^2 + 63*z0^2*z1^2*z2 + 3*z0^2*z2^3 + 27*z0*z1^4 - 15*z0*z1^2*z2^2 + 15
  6*z1^4*z2 - 162*z1^2*z2^3

julia> radical(I)
Ideal generated by
  z0^3 - 9*z0*z1^2 - 3*z0*z2^2 - 6*z1^2*z2
  z0^2*z2^2 - 50*z0*z1^2*z2 - 18*z0*z2^3 + 28*z1^4 - 63*z1^2*z2^2
  7*z0^2*z1*z2 + 56*z0*z1^3 + 18*z0*z1*z2^2 + 45*z1^3*z2 - 9*z1*z2^3
  28*z0^2*z1^2 + 9*z0^2*z2^2 + 54*z0*z1^2*z2 + 6*z0*z2^3 + 21*z1^2*z2^2
```
"""
function get_stratum_smooth_curve(f, k)
    R, vars = polynomial_ring(QQ, vcat(["x","y","z"], ["X", "Y", "Z"]))
    (x,y,z) = vars[1:3]
    (X,Y,Z) = vars[4:6]
    A = base_ring(ideal([f]))
    alpha = hom(A, R, [x,y,z])
    f = alpha(f)

    I = ideal([X - derivative(f, x), Y - derivative(f, y), Z - derivative(f, z)]) + ideal([f])
    Cdual = eliminate(I, [x,y,z])

    S, z = graded_polynomial_ring(QQ, ["z$i" for i in 0:2])
    K = fraction_field(S)
    T, (X,Y,Z) = polynomial_ring(K, ["X", "Y", "Z"])
    phi = hom(R, T, vcat(T.(Int.(zeros(3))), [X,Y,Z]))
    Cdual = phi(Cdual)
    H = ideal([X - z[1]//1, Y - z[2]//1, Z - z[3]//1])

    F = gens(Cdual)[1]
    Q, pho = quo(T, H^k)
    M = monomial_basis(Q)
    comp_matrix_entries = vcat([collect(Oscar.coefficients(lift(simplify(pho(F*m))))) for m in M]...)
    J = ideal(S.(numerator.(comp_matrix_entries)))
    return minimal_generating_set(J)
end