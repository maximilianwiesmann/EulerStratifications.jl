using Oscar
using Combinatorics
using HomotopyContinuation

export get_stratum_equations, get_stratum_numerically, univariate_strata, univariate_strata_projective


@doc raw"""
    get_stratum_equations(stratum::Tuple{Vector{Int}, Tuple{Int, Int}}; K=QQ)

Return generators of the ideal of the Euler stratum of the form ([λ],(m\_0,m\_∞)),
optionally choose field K

## Example

```jldoctest
julia> stratum = ([2,1], (0,1))
([2, 1], (0, 1))

julia> get_stratum_equations(stratum)
2-element Vector{QQMPolyRingElem}:
 z5
 -27*z1^2*z4^2 + 18*z1*z2*z3*z4 - 4*z1*z3^3 - 4*z2^3*z4 + z2^2*z3^2
```
"""
function get_stratum_equations(stratum; K = QQ)
    deg = sum(stratum[1]) + sum(stratum[2])
    S, t = polynomial_ring(K, ["t$i" for i in 1:deg+1])
    R, x = polynomial_ring(S, ["x1", "x2"])
    poly = x[1]^(stratum[2][1])*x[2]^(stratum[2][2])*prod([(x[1] - t[i]*x[2])^(stratum[1][i]) for i in 1:length(stratum[1])])
    coeffs = [Oscar.evaluate(t[end]*R(coeff(poly, x, [i, deg - i])), [0,0]) for i in 0:deg]
    T, z = polynomial_ring(K, ["z$i" for i in 1:length(coeffs)])
    f = hom(T, S, coeffs)
    return gens(kernel(f))
end


# get all monomials of a given multidegree deg
# the multigrading is specified by A
function get_monomials_of_deg(A, deg)
    d = deg[1]
    @var z[1:size(A, 2)]
    E, _  = exponents_coefficients(sum(z)^d,z)
    dgs = A*E
    return E[:,findall(i -> dgs[:,i] == deg, 1:size(dgs,2))]
end


# get all equations in a given multidegree,
# interpolating the given samples 
function equations_for_multidegree(A, samples, multideg, z_red; K=QQ)
    ngens = 0
    gens = []
    mtx = get_monomials_of_deg(A, multideg)
    vdm = transpose(hcat([[prod(s.^mtx[:,j]) for j = 1:size(mtx,2)] for s in samples]...))
    NSdim, NS = nullspace(matrix_space(K,size(vdm)...)(vdm))
    if NSdim > 0
        ngens += NSdim
        mons = [prod(z_red.^mtx[:,j]) for j = 1:size(mtx,2)]
        newgens = transpose(NS)*mons
        push!(gens, newgens...)
    end
    return gens
end


# create nsamples samples on the variety parametrized by coeffs_red
function create_sample(coeffs_red, nsamples; K=QQ)
    u = variables(coeffs_red)
    if K == ComplexF64 || K == Float64
        samples = [HomotopyContinuation.evaluate.(coeffs_red, u=>randn(K,length(u))) for i = 1:nsamples]
    elseif typeof(K) == FqField
        samples = [K.(Int.(HomotopyContinuation.evaluate.(coeffs_red, u=>rand(1:100,length(u))))) for i = 1:nsamples]
    elseif K == QQ
        samples = [Rational{BigInt}.(HomotopyContinuation.subs(coeffs_red, u=>rand(-50:50,length(u))//rand(1:50))) for i = 1:nsamples]
    end
    return samples
end


# return generators od degree d of ideal of Euler stratum via interpolation
# homogeneous wrt a given multigrading defined by A
function numerical_univariate_stratum(d, A, stratum; K=QQ, verbose=false)
    deg = sum(stratum[1]) + sum(stratum[2])
    if typeof(K) == FqField || K == QQ
        R, z = graded_polynomial_ring(K,["z$i" for i = 1:deg+1]) 
    else
        @var z[1:deg+1]
    end
    @var u[1:deg+1]

    S, t = polynomial_ring(QQ, ["t$i" for i in 1:deg+1])
    R, x = polynomial_ring(S, ["x1", "x2"])
    poly = x[1]^(stratum[2][1])*x[2]^(stratum[2][2])*prod([(x[1] - t[i]*x[2])^(stratum[1][i]) for i in 1:length(stratum[1])])
    coeffs = [oscar_to_HC_Q(Oscar.evaluate(t[end]*R(coeff(poly, x, [i, deg - i])), [0,0]), u) for i in 0:deg]
    nonzero_coeffs = findall(i -> i != 0, coeffs)
    z_red = z[nonzero_coeffs]
    coeffs_red = coeffs[nonzero_coeffs]
    E, C = exponents_coefficients(sum(u[nonzero_coeffs])^d, u[nonzero_coeffs])
    A = A[:, nonzero_coeffs]

    degs = A*E
    cols = [degs[:,j] for j = 1:size(degs,2)]
    graded_buckets = [findall(i -> degs[:,i] == c, 1:size(degs,2)) for c in unique(cols)]
    nsamples = Int(round(maximum(length.(graded_buckets))*1.5))

    samples = create_sample(coeffs_red, nsamples; K=K)
    gens = []
    if length(stratum[1]) > 1
        if stratum[1][1] == 2 && stratum[1][2] == 1
            deg_univ = sum(stratum[1])
            deg_discr = 2*deg_univ - 2
            A = transpose(hcat([Int.(ones(length(z_red))), 1:length(z_red)]...))
            return append!(gens, vcat(z[setdiff(1:deg+1, nonzero_coeffs)], equations_for_multidegree(A, samples, [deg_discr, numerator(deg_discr*(deg_discr+1)//2)], z_red; K=K)))
        end
    end

    correct_cols = unique(cols)
    for i = 1:length(graded_buckets)
        if verbose
            println("current bucket: $(correct_cols[i]) out of $(length(graded_buckets))")
        end
        append!(gens, equations_for_multidegree(A, samples, correct_cols[i], z_red; K=K))
    end
    append!(gens, z[setdiff(1:deg+1, nonzero_coeffs)])
    return gens
end

@doc raw"""
    get_strata_numerically(stratum::Tuple{Vector{Int}, Tuple{Int, Int}}; K=QQ, max_deg=-1, verbose=false)

Return generators of the ideal for Euler stratum by interpolation
if max\_deg is provided, look for generators of degree <= max\_deg
if not, stop when the ideal has expected dimension and degree
if test\_equidimensional, also check for equidimensionality via numerical
irreducible decomposition

## Example

```jldoctest
julia> stratum = ([2, 1], (1, 0))
([2, 1], (1, 0))

julia> get_stratum_numerically(stratum)
2-element Vector{Any}:
 z1
 -27*z2^2*z5^2 + 18*z2*z3*z4*z5 - 4*z2*z4^3 - 4*z3^3*z5 + z3^2*z4^2
```
"""
function get_stratum_numerically(stratum; K=QQ, max_deg=-1, test_equidimensional=false, verbose=false)
    deg = sum(stratum[1]) + sum(stratum[2])
    A = transpose(hcat(Int.(ones(deg+1)), 0:deg))
    geners = []
    if length(stratum[1]) > 1   # check for discriminant case 
        if stratum[1][1] == 2 && stratum[1][2] == 1
            deg_univ = sum(stratum[1])
            if verbose 
                println("currently looking for equations in degree $(2*deg_univ-2) for stratum $(stratum)")
            end
            return numerical_univariate_stratum(2*deg_univ-2, A, stratum; K=K, verbose=verbose)
        end
    end
    if !is_empty(stratum[1])
        if all(i -> i == 1, stratum[1]) && stratum[2] == (0,0)
            if verbose
                println("abort stratum")
            end
            return [0]
        end
    end
    d = 1
    if stratum[1][1] == 0
        expected_dim = 0
    else
        expected_dim = length(stratum[1])
    end
    if max_deg > 0      # max_deg provided, then look for equs in d <= max_deg
        while d <= max_deg 
            if verbose 
                println("currently looking for equations in degree $d for stratum $(stratum)")
            end
            newgens = numerical_univariate_stratum(d, A, stratum; K=K, verbose=verbose)
            append!(geners,newgens)
            if stratum[1] == [0] 
                return geners
            end
            d = d + 1
        end
        return geners
    end
    while true
        if verbose
            println("currently looking for equations in degree $d for stratum $(stratum)")
        end
        newgens = numerical_univariate_stratum(d, A, stratum; K=K, verbose=verbose)
        append!(geners,newgens)
        if stratum[1] == [0]    # check manually as HC won't work in this case
            return geners
        end
        if verbose
            println("found $(length(newgens)) new generators")
        end
        if !is_empty(geners)
            if (typeof(K) == FqField || K == QQ) && Oscar.dim(ideal(geners)) == expected_dim + 1
                redgens = minimal_generating_set(ideal(geners))
                if verbose
                    println("reduced to $(length(redgens)) generators")
                    println("computing degree with Oscar...")
                end
                deg_geners = Oscar.degree(ideal(redgens))
                if verbose
                    println("degree computed with Oscar: $(deg_geners)")
                end
                vrs = gens(base_ring(ideal(geners)))
                @var t[1:length(vrs)]
                num = factorial(length(stratum[1]))*prod(stratum[1])
                den = prod([factorial(sum(stratum[1].==i)) for i = 1:length(vrs)-1])
                degr = Int(num//den)
                if verbose
                    println("expected degree: $degr")
                end
                redgens_HC = [oscar_to_HC_Q(f,t) for f in redgens]
                if deg_geners == degr 
                    if length(redgens) == 1 
                        if expected_dim + 1 == deg
                            return redgens
                        end
                    elseif test_equidimensional
                        if verbose
                            println("computing numerical irreducible decomposition")
                        end
                        NID = nid(System(redgens_HC))
                        WS = NID.Witness_Sets
                        if length(WS) == 1
                            return redgens
                        elseif verbose
                            println("NOT EQUIDIMENSIONAL")
                        end
                    else
                        return redgens
                    end
                end
            end
        end
        d = d + 1
    end
    return nothing
end


# auxiliary function for evaluation in polynomial ring, possibly with variable shift
function proper_evaluate(g, R; shift=0)
    if typeof(g) == Int
        return R(g)
    else
        return Oscar.evaluate(g, gens(R)[1+shift:length(gens(base_ring(ideal([g]))))+shift])
    end
end


@doc raw"""
    univariate_strata(deg::Int; numerically=false, K=QQ, compute_discriminants=true, compute_221=true, max_degs=Dict())

Return the Euler stratification for a univariate polynomial of degree deg in C^*
computation is done symbolically unless numerically=true, then use interpolation
computation of discriminants and strata with partitions of the form (2,2,1,...) 
can be turned off (saves time)
a dictionary with maximal degrees can be provided, then the interpolation gets 
polynomials up to the max\_deg provided

## Example

```jldoctest
julia> univariate_strata(3)
Dict{Tuple{Vector{Int64}, Tuple{Int64, Int64}}, Oscar.MPolyIdeal{Oscar.MPolyDecRingElem{Nemo.QQFieldElem, Nemo.QQMPolyRingElem}}} with 14 entries:
  ([1, 1], (1, 0))    => Ideal (0, z0)
  ([3], (0, 0))       => Ideal (-3*z1*z3 + z2^2, -9*z0*z3 + z1*z2, -3*z0*z2 + z…
  ([0], (2, 1))       => Ideal (z0, z1, z3)
  ([1], (1, 1))       => Ideal (0, z0, z3)
  ([1], (2, 0))       => Ideal (0, z0, z1)
  ([1, 1], (0, 1))    => Ideal (0, z3)
  ([1, 1, 1], (0, 0)) => Ideal (0)
  ([0], (1, 2))       => Ideal (z0, z2, z3)
  ([2], (1, 0))       => Ideal (-4*z1*z3 + z2^2, z0)
  ([2, 1], (0, 0))    => Ideal (-27*z0^2*z3^2 + 18*z0*z1*z2*z3 - 4*z0*z2^3 - 4*…
  ([0], (0, 3))       => Ideal (z1, z2, z3)
  ([0], (3, 0))       => Ideal (z0, z1, z2)
  ([1], (0, 2))       => Ideal (0, z2, z3)
  ([2], (0, 1))       => Ideal (-4*z0*z2 + z1^2, z3)
```
"""
function univariate_strata(deg; numerically=false, K=QQ, compute_discriminants=true, compute_221=true, max_degs=Dict(), verbose=false)

    strata_label = []
    for i in 0:deg
        part = Combinatorics.partitions(i)
        boundaries = []
        for j in 0:(deg-i)
            push!(boundaries, (j, deg-i-j))
        end
        if i == 0
            append!(strata_label, [([0], b) for b in boundaries])
        else    
            for (p, b) in Iterators.product(part, boundaries)
                push!(strata_label, (p, b))
            end
        end
    end
    strata_equations = []
    strata_wo_boundary = [c for c in vcat([collect(Combinatorics.partitions(i)) for i in 1:deg]...)]
    temp_strata_equations = []
    R, z = graded_polynomial_ring(K, ["z$i" for i in 0:deg])
    try
        for (num_s, s) in enumerate(strata_wo_boundary)
            if verbose
                println("computing stratum " * string(s) * "(" * string(num_s) * " out of " * string(length(strata_wo_boundary))) * ")"
            end
            if !compute_discriminants && length(s) > 1
                if s[1] == 2 && s[2] == 1 
                    push!(temp_strata_equations, [0])
                    continue
                end
            end
            if !compute_221 && length(s) > 2
                if s[1] == 2 && s[2] == 2 && s[3] == 1
                    push!(temp_strata_equations, [0])
                    continue
                end
            end
            if !numerically
                push!(temp_strata_equations, get_stratum_equations((s, (0,0)); K=K))
            else
                if is_empty(max_degs)
                    push!(temp_strata_equations, get_stratum_numerically((s, (0,0)); K=K, verbose=verbose))
                else
                    max_deg = max_degs[(s, (deg - sum(s), 0))]
                    push!(temp_strata_equations, get_stratum_numerically((s, (0,0)); K=K, max_deg=max_deg, verbose=verbose))
                end
            end
        end
        temp_strati = Dict([t for t in tuple.(strata_wo_boundary, temp_strata_equations)])
        for s in strata_label
            if s[1] == [0]
                push!(strata_equations, ideal(vcat(z[1:s[2][1]], z[end-s[2][2]+1:end])))
            else
                temp_equs = [proper_evaluate(e, R, shift=s[2][1]) for e in temp_strati[s[1]]]
                append!(temp_equs, vcat(z[1:s[2][1]], z[end-s[2][2]+1:end]))
                push!(strata_equations, ideal(temp_equs))
            end
        end
    catch e
        if isa(e, InterruptException)
            println("Computation interrupted")
            no_results = ["stratum not computed" for i in 1:(length(strata_wo_boundary)-length(temp_strata_equations))]
            temp_strati = Dict([t for t in tuple.(strata_wo_boundary, vcat(temp_strata_equations, no_results))])
            for s in strata_label
                if s[1] == [0]
                    push!(strata_equations, ideal(vcat(z[1:s[2][1]], z[end-s[2][2]+1:end])))
                elseif typeof(temp_strati[s[1]]) == String
                    push!(strata_equations, "stratum not computed")
                else
                    temp_equs = [proper_evaluate(e, R, shift=s[2][1]) for e in temp_strati[s[1]]]
                    append!(temp_equs, vcat(z[1:s[2][1]], z[end-s[2][2]+1:end]))
                    push!(strata_equations, ideal(temp_equs))
                end
            end
            return Dict([t for t in tuple.(strata_label, strata_equations)])
        else
            rethrow(e)
        end
    end
    return Dict([t for t in tuple.(strata_label, strata_equations)])
end


@doc raw"""
    univariate_strata_projective(deg::Int; numerically=false, K=QQ, compute_discriminants=true, compute_221=true, max_degs=Dict())

Return the Euler stratification for a univariate polynomial of degree deg in P^1
computation is done symbolically unless numerically=true, then use interpolation
computation of discriminants and strata with partitions of the form (2,2,1,...) 
can be turned off (saves time)
a dictionary with maximal degrees can be provided, then the interpolation gets 
polynomials up to the max\_deg provided

##Example

```jldoctest
julia> univariate_strata_projective(3)
Dict{Vector{Int64}, Vector{Oscar.MPolyDecRingElem{Nemo.QQFieldElem, Nemo.QQMPolyRingElem}}} with 3 entries:
  [2, 1]    => [-27*z0^2*z3^2 + 18*z0*z1*z2*z3 - 4*z0*z2^3 - 4*z1^3*z3 + z1^2*z…
  [3]       => [-3*z1*z3 + z2^2, -9*z0*z3 + z1*z2, -3*z0*z2 + z1^2]
  [1, 1, 1] => [0]
```
"""
function univariate_strata_projective(deg; numerically=false, K=QQ, compute_discriminants=true, compute_221=true, max_degs=Dict(), verbose=false)
    strata_label = [p for p in Combinatorics.partitions(deg)]
    strata_equations = []
    R, z = graded_polynomial_ring(K, ["z$i" for i in 0:deg])
    try
        for (num_s, s) in enumerate(strata_label)
            if verbose
                println("computing stratum " * string(s) * "(" * string(num_s) * " out of " * string(length(strata_label))) * ")"
            end
            if !compute_discriminants && length(s) > 1
                if s[1] == 2 && s[2] == 1 
                    push!(strata_equations, [proper_evaluate(0, R)])
                    continue
                end
            end
            if !compute_221 && length(s) > 2
                if s[1] == 2 && s[2] == 2 && s[3] == 1
                    push!(strata_equations, [proper_evaluate(0, R)])
                    continue
                end
            end
            if !numerically
                push!(strata_equations, [proper_evaluate(e, R) for e in get_stratum_equations((s, (0,0)); K=K)])
            else
                if is_empty(max_degs)
                    push!(strata_equations, [proper_evaluate(e, R) for e in get_stratum_numerically((s, (0,0)); K=K, verbose=verbose)])
                else
                    max_deg = max_degs[(s, (deg - sum(s), 0))]
                    push!(strata_equations, [proper_evaluate(e, R) for e in get_stratum_numerically((s, (0,0)); K=K, max_deg=max_deg, verbose=verbose)])
                end
            end
        end
    catch e
        if isa(e, InterruptException)
            println("Computation interrupted")
            no_results = ["stratum not computed" for i in 1:(length(strata_label)-length(strata_equations))]
            return Dict([t for t in tuple.(strata_label, vcat(strata_equations, no_results))])
        else
            rethrow(e)
        end
    end
    return Dict([t for t in tuple.(strata_label, strata_equations)])
end


# given a stratification (e.g. over a finite field), get the maximal degrees
# of a generating set of the ideals
# output can be used as an optional input to univariate_strata
function get_max_degrees(strati)
    strati_keys = collect(keys(strati))
    max_degs = Dict([t for t in tuple.(strati_keys, Int.(zeros(length(strati_keys))))])
    for k in strati_keys
        I = strati[k]
        if I == ideal([base_ring(I)(0)])
            if length(k[1]) > 1
                if k[1][1] == 2 && k[1][2] == 1     # discriminant case
                    max_degs[k] = 2*length(k[1])
                end
            end
            if length(k[1]) > 2
                if k[1][1:3] == [2,2,1]     # (2,2,1,...) case
                    max_degs[k] = 2*length(k[1]) - 1
                end
            end
            continue
        end
        degs = [Oscar.degree(Int, g) for g in gens(I) if g != base_ring(I)(0)]
        max_degs[k] = maximum(degs)
    end
    return max_degs
end
