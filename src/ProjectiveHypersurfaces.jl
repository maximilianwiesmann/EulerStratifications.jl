using Oscar
using IterTools
using HomotopyContinuation
using LinearAlgebra

export get_euler_char, get_polar_discriminant, get_euler_discriminant_proj


"""
    get_euler_char(F::Expression; method = :restrict)

Compute the Euler characteristic of a hypersurface complement defined by F.
Choose method of computation: via restriction of Gauss map (:restrict) or 
via cohomology class of the graph of the Gauss map (:graph)

## Example

```jldoctest
julia> @var x[0:2]
(Variable[x₀, x₁, x₂],)

julia> F = x[1]^3 + x[2]^2*x[3]
x₂*x₁^2 + x₀^3

julia> get_euler_char(F)
degree of ∇F restricted to H2 = 2
degree of ∇F restricted to H1 = 2
degree of ∇F restricted to H0 = 1
1
```
"""
function get_euler_char(F; method = :restrict)
    x = variables(F)
    d = length(x)-1
    if method == :graph
        @var y[1:d+1]
        @var w
        M = [differentiate(F,x) y]
        Eqs = [det(M[s,:]) for s in IterTools.subsets(1:d+1,2)]
        degs = []
        for i = 0:d
            lineqs = [randn(i+1,d+1)*x + randn(i+1); randn(d-i+1,d+1)*y + randn(d-i+1)]
            R = HomotopyContinuation.solve([Eqs;lineqs;1-w*F]; show_progress=false)
            push!(degs,(-1)^i*length(solutions(R)))
            println("e$(d-i) = $(abs(degs[end]))")
        end
        return sum(degs)
    elseif method == :restrict
        @var w v
        degs = []
        for i = d:-1:0
            myL = randn(ComplexF64,d+1,i+1)
            Fres = subs(F,x=>myL*x[1:i+1])
            grad = differentiate(Fres,x[1:i+1])
            b = randn(ComplexF64,i+1)
            vv = randn(ComplexF64,2) + v.*randn(ComplexF64,2)
            eqs = [[grad b]*vv; 1-w*Fres; dot(randn(ComplexF64,i+1),x[1:i+1]) + randn(ComplexF64)]
            R = HomotopyContinuation.solve(eqs; show_progress=false)
            push!(degs,(-1)^i*length(solutions(R)))
            println("degree of ∇F restricted to H$i = $(abs(degs[end]))")
        end
        return sum(degs)
    end
end


""" 
    get_polar_discriminant(F::MPolyRingElem, Rz::MPolyRing, Rx::MPolyRing, Iz::MPolyIdeal; decompose=true, randrange=-100:100, verbose=false)

Compute the polar discriminant of the hypersurface family defined by F.

## Example

```jldoctest
julia> d, m = 2,5
(2, 5)

julia> Rz, z = graded_polynomial_ring(QQ,["z$i" for i = 1:m+1])
(Graded multivariate polynomial ring in 6 variables over QQ, MPolyDecRingElem{QQFieldElem, QQMPolyRingElem}[z1, z2, z3, z4, z5, z6])

julia> Rx, x = polynomial_ring(Rz,["x$i" for i = 1:d+1])
(Multivariate polynomial ring in 3 variables over Rz, AbstractAlgebra.Generic.MPoly{MPolyDecRingElem{QQFieldElem, QQMPolyRingElem}}[x1, x2, x3])

julia> F = z[1]*x[1]^2 + z[2]*x[1]*x[2] + z[3]*x[1]*x[3] + z[4]*x[2]^2 + z[5]*x[2]*x[3] + z[6]*x[3]^2
z1*x1^2 + z2*x1*x2 + z3*x1*x3 + z4*x2^2 + z5*x2*x3 + z6*x3^2

julia> Iz = ideal([Rz(0)])
Ideal generated by
  0

julia> PD = get_polar_discriminant(F, Rz, Rx, Iz)
1-element Vector{MPolyIdeal{MPolyDecRingElem{QQFieldElem, QQMPolyRingElem}}}:
 Ideal (4*z1*z4*z6 - z1*z5^2 - z2^2*z6 + z2*z3*z5 - z3^2*z4)
```
"""
function get_polar_discriminant(F, Rz, Rx, Iz; decompose=true, randrange=-100:100, verbose=false)
    dimZ = Oscar.dim(Iz)-1
    d = length(gens(Rx))-1
    FF, R, x, z, w, psi, phi = to_big_ring(F,Rx,Rz)
    E = ideal([Rz(0)])
    for j = 1:dimZ+1
        if verbose
            println("random parameter choice $j out of $(dimZ + 1)")
        end
        grad = [derivative(FF,xx) for xx in x]
        b = R.(rand(randrange,d+1)) 
        eqs = [grad b]*[w;rand(randrange)+rand(randrange)*w]
        II = ideal(eqs) + psi(Iz)
        Isat = saturation(II,ideal([FF]))
        J = eliminate(Isat + ideal([FF]) + ideal([sum(x)-1]),[x;w])
        E = E + phi(J)
    end
    if decompose 
        MP = minimal_primes(E)
        return MP[findall(mp->mp != ideal(gens(Rz)), MP)]
    else
        return E
    end
end


"""
    get_euler_discriminant_proj(F::MPolyRingElem, Rz::MPolyRing, Rx::MPolyRing, Iz::MPolyIdeal; randrange=-100:100, verbose=false)

Compute the Euler discriminant of the hypersurface family defined by F in projective space.

## Example

```jldoctest
julia> d, m = 2,5
(2, 5)

julia> Rz, z = graded_polynomial_ring(QQ,["z$i" for i = 1:m+1])
(Graded multivariate polynomial ring in 6 variables over QQ, MPolyDecRingElem{QQFieldElem, QQMPolyRingElem}[z1, z2, z3, z4, z5, z6])

julia> Rx, x = polynomial_ring(Rz,["x$i" for i = 1:d+1])
(Multivariate polynomial ring in 3 variables over Rz, AbstractAlgebra.Generic.MPoly{MPolyDecRingElem{QQFieldElem, QQMPolyRingElem}}[x1, x2, x3])

julia> F = z[1]*x[1]^2 + z[2]*x[1]*x[2] + z[3]*x[1]*x[3] + z[4]*x[2]^2 + z[5]*x[2]*x[3] + z[6]*x[3]^2
z1*x1^2 + z2*x1*x2 + z3*x1*x3 + z4*x2^2 + z5*x2*x3 + z6*x3^2

julia> Iz = ideal([Rz(0)])
Ideal generated by
  0

julia> get_euler_discriminant_proj(F, Rz, Rx, Iz)
1-element Vector{MPolyIdeal{MPolyDecRingElem{QQFieldElem, QQMPolyRingElem}}}:
 Ideal (4*z1*z4*z6 - z1*z5^2 - z2^2*z6 + z2*z3*z5 - z3^2*z4)
```
"""
function get_euler_discriminant_proj(F, Rz, Rx, Iz; randrange=-100:100, verbose=false) 
    d = length(gens(Rx))-1
    comps = []
    dimZ = Oscar.dim(Iz) - 1 
    for i = d:-1:1
        if verbose 
            println("----------------- restricting to subspace of dimension $i")
        end
        S, xt = polynomial_ring(Rz,["x$j" for j = 1:i+1])
        E = ideal([Rz(0)])
        klim = i<d ? dimZ + 1 : 1
        for k = 1:klim
            T = vcat(identity_matrix(S, i+1), matrix_space(S, d-i, i+1)((rand(randrange, d-i, i+1))))
            ϕ = hom(Rx, S, T*xt)
            Fres = ϕ(F)
            E = E + get_polar_discriminant(Fres, Rz, S, Iz; randrange=randrange, decompose=false)
            if verbose
                println("k = $k, E = $E")
            end
        end
        if verbose 
            println("E has $(length(gens(E))) generators. Computing minimal generating set...")
        end
        E = ideal(minimal_generating_set(E))
        MP = minimal_primes(E)
        push!(comps,MP...)
        if verbose 
            println("minimal primes:")
            println("MP = $(MP)")
        end
    end
    if !isempty(comps)
        MP = minimal_primes(intersect(comps...))
        return MP[findall(mp->mp != ideal(gens(Rz)), MP)]
    else
        return comps
    end
    own_unique!(comps)
end



