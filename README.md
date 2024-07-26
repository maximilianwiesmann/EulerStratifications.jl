# EulerStratifications.jl


**EulerStratifications.jl** is Julia package to compute Euler stratifications and related objects (Euler discriminants, polar discriminants, ...). It accompanies the paper **Euler Stratifications of Hypersurface Families** ([arXiv:2407.18176](https://arxiv.org/abs/2407.18176)).

---

## Installation

You can directly install the package from Github by running the following commands in a Julia terminal:

```julia
import Pkg
Pkg.add(url="https://github.com/maximilianwiesmann/EulerStratifications.jl")
using EulerStratifications
```

You might also want to use the computer algebra software package [Oscar](https://docs.oscar-system.org/stable/) and the numerical algebraic geometry package [HomotopyContinuation](https://www.juliahomotopycontinuation.org/HomotopyContinuation.jl/stable/):

```julia
using Oscar
using HomotopyContinuation
```

```@docs
get_stratum_numerically
```