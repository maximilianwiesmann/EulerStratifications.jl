using Oscar
using HomotopyContinuation


# auxiliary function to only get unique elements of vector
function own_unique!(itr)
    seen = Vector{eltype(itr)}()
    goodinds = []
    for i in 1:length(itr)
        if !isempty(findall(j->j==itr[i],seen)) 
            # If x has already been encountered in itr, remove it
        else
            # Otherwise note that we've encountered it
            push!(goodinds,i)
            push!(seen, itr[i])
        end
    end
    return itr[goodinds]
end


# auxiliary function returning a representation FF of F ∈ Rx = Rz[x]
# in the ring R with variables x, z and w, together with a map 
# phi from R to Rz and a map psi from Rz to R
function to_big_ring(F, Rx, Rz)
    d = length(gens(Rx))-1
    m = length(gens(Rz))-1
    R, vrs = polynomial_ring(QQ,[["x$i" for i = 1:d+1];["z$j" for j = 1:m+1];"w"])
    x = vrs[1:d+1]
    z = vrs[d+2:d+m+2]
    w = vrs[end]
    C = collect(Oscar.coefficients(F))
    E = collect(Oscar.exponents(F))
    FF = sum([Oscar.evaluate(C[i],z)*prod(x.^E[i]) for i = 1:length(C)])
    psi = hom(Rz,R,z)
    phi = hom(R,Rz,[Rz.(ones(Int,d+1));gens(Rz);Rz(1)])
    return FF, R, x, z, w, psi, phi
end


# auxiliary function to convert Oscar polynomial f to HomotopyContinuation expression
# in the variables vars; f should have rational coefficients
function oscar_to_HC_Q(f, vars)
    cffs = convert.(Rational{Int64},collect(Oscar.coefficients(f)))
    exps = collect(Oscar.exponents(f))
    return sum([cffs[i]*prod(vars.^exps[i]) for i = 1:length(cffs)])
end


# auxiliary function to convert Oscar polynomial f to HomotopyContinuation expression
# where f has coefficients in a polynomial ring S over Q
# output contains new variables and parameters of the expression of f
function oscar_to_HC_S(f, S)
    R = base_ring(f)
    n = nvars(S) # number of variables
    @var x[1:n]
    m = nvars(R) # number of parameters
    @var a[1:m]
    cffs_oscar = collect(Oscar.coefficients(f))
    cffs_HC = [oscar_to_HC_Q(g,a) for g in cffs_oscar]
    exps = collect(Oscar.exponents(f))
    mons_HC = [prod(x.^exps[i]) for i = 1:length(exps)]
    return sum([cffs_HC[i]*mons_HC[i] for i = 1:length(cffs_HC)]), x, a
end


# return a generic point on the stratum defined by the input ideal
function get_sample(stratum)
    z = gens(base_ring(stratum))
    m = length(z)-1
    @var Z[1:m+1]
    if stratum == ideal([base_ring(stratum)(0)])
        return randn(ComplexF64,m+1)
    end
    gens_HC = [oscar_to_HC_Q(g,Z) for g in gens(stratum)]
    sols = []; i = 1;
    for j = 1:m-length(gens_HC)
        gens_HC = [gens_HC; sum([randn(ComplexF64)*Z[i] for i = 1:m+1])]
    end
    while isempty(sols) && i < 10
        R = HomotopyContinuation.solve([gens_HC; sum([randn(ComplexF64)*Z[i] for i = 1:m+1])-randn(ComplexF64)])  #random dehomogenization
        sols = solutions(R)
        gens_HC = [gens_HC; sum([randn(ComplexF64)*Z[i] for i = 1:m+1]) ]
        i+=1
    end
    return sols[1]
end