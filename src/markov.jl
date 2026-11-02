# Research extension, beyond the papers: stochastic cellular automata as morphisms of a Markov
# category. A stochastic CA draws each cell's new state from a local kernel of the states on its
# memory set, independently across cells given the input. Copying is no longer natural (a run copied
# is not two runs), and a pair of stochastic CA with given marginals is not unique: it needs a choice
# of coupling. Exact distributions are computed by enumeration on small groups; on CellularAutomataCore
# a kernel is sampled with the counter-based uniform draw numbered `draw`.

"""
    StochasticCA(G, S, κ; dom, codom=dom)
    StochasticCA(τ::CellularAutomaton)

A stochastic cellular automaton over the group `G`. This is a research
extension, beyond the categorical framework of the papers, which covers
deterministic automata. The local kernel `κ` maps the tuple of states on the
memory set `S` to a vector of probabilities over the values of the alphabet
`codom`, in order. Each cell's new state is drawn from the kernel of its own
pattern, independently of the other cells given the input configuration.
The second form is a deterministic cellular automaton, as a kernel of point
masses.

Stochastic automata are morphisms of a Markov category, not of a cartesian
one: copying the output of a run is not the same as running twice, and two
stochastic automata from the same domain pair in many ways, one for each
coupling of their random draws ([`stochastic_pair`](@ref)).
[`distribution`](@ref) computes exact output distributions on small groups.
On CellularAutomataCore, `LocalRule(T; draw)` samples one, and
`CAProblem(T, u0, tspan; draw)` builds a problem from it.
"""
struct StochasticCA{G,E,F,D<:FullShift,C<:FullShift}
    group::G
    memory::Vector{E}
    kernel::F
    dom::D
    codom::C
end
function StochasticCA(G::AbstractFiniteGroup, S::AbstractVector, κ;
                      dom::Union{FinAlphabet,FullShift},
                      codom::Union{FinAlphabet,FullShift}=dom)
    foreach(s -> _check_member(G, s, "memory set"), S)
    allunique(S) || throw(ArgumentError("the memory set has repeated elements: $S"))
    return StochasticCA(G, collect(S), κ, _shift_over(dom, G), _shift_over(codom, G))
end
function StochasticCA(τ::CellularAutomaton)
    values = alphabet(τ.codom).values
    κ = p -> (v=τ.rule(p); [x == v ? 1.0 : 0.0 for x in values])
    return StochasticCA(τ.group, τ.memory, κ, τ.dom, τ.codom)
end

group(T::StochasticCA) = T.group
dom(T::StochasticCA) = T.dom
codom(T::StochasticCA) = T.codom
memory_set(T::StochasticCA) = T.memory
function Base.show(io::IO, T::StochasticCA)
    print(io, "StochasticCA over ", T.group, " with memory set ", T.memory, ": ")
    _show_shift(io, T.dom)
    print(io, " → ")
    return _show_shift(io, T.codom)
end

# The kernel at one cell, checked to be a probability vector.
function _cell_kernel(T::StochasticCA, x::Configuration, g)
    G = T.group
    q = T.kernel(Tuple(x[mul(G, s, g)] for s in T.memory))
    n = length(alphabet(T.codom))
    (length(q) == n && all(>=(0), q) && isapprox(sum(q), 1; atol=1e-9)) ||
        throw(ArgumentError("the kernel must return $n probabilities summing to 1, got $q"))
    return q
end

"""
    distribution(T::StochasticCA, x) -> Dict{Configuration,Float64}
    distribution(T::StochasticCA, d::AbstractDict) -> Dict{Configuration,Float64}

The exact distribution of the output of a stochastic cellular automaton: for
an input configuration `x`, the product of the cells' kernels; for a
distribution `d` of inputs (configurations to probabilities), the mixture over
them, which is how two stochastic automata compose. Outcomes of probability 0
are left out. The number of outcomes is at most `|B|^|G|`, so this is for small
groups; it raises `ArgumentError` beyond 65536 possible outcomes.
"""
function distribution(T::StochasticCA, x::Configuration)
    G = T.group
    x.group == G || throw(GroupMismatchError("a stochastic cellular automaton", G, x.group))
    values = alphabet(T.codom).values
    big(length(values))^length(G) <= CONFIGURATION_LIMIT ||
        throw(ArgumentError("$(length(values))^$(length(G)) outcomes are too many to enumerate"))
    E = collect(elements(G))
    partial = Dict{Vector{eltype(values)},Float64}(eltype(values)[] => 1.0)
    for g in E
        q = _cell_kernel(T, x, g)
        next = Dict{Vector{eltype(values)},Float64}()
        for (prefix, pr) in partial, (k, v) in enumerate(values)
            q[k] > 0 || continue
            next[vcat(prefix, [v])] = pr * q[k]
        end
        partial = next
    end
    return Dict(Configuration(G, reshape(cells, shape(G))) => pr for (cells, pr) in partial)
end
function distribution(T::StochasticCA, d::AbstractDict)
    out = Dict{Configuration,Float64}()
    for (x, px) in d, (y, py) in distribution(T, x)
        out[y] = get(out, y, 0.0) + px * py
    end
    return out
end

"""
    marginal(d, f) -> Dict

The distribution of `f(x)` when `x` has the distribution `d`, a dictionary of
outcomes to probabilities, such as the joint distribution of two cells,
`marginal(d, y -> (y[0], y[1]))`.
"""
function marginal(d::AbstractDict, f)
    out = Dict{Any,Float64}()
    for (x, p) in d
        k = f(x)
        out[k] = get(out, k, 0.0) + p
    end
    return out
end

# The comonotone coupling of two probability vectors: both values from one uniform draw.
function _shared_coupling(q, r)
    Q, R = cumsum(q), cumsum(r)
    edges = sort!(unique!(vcat(0.0, Q, R)))
    joint = zeros(length(q), length(r))
    for k in 1:(length(edges) - 1)
        lo, hi = edges[k], edges[k + 1]
        hi > lo || continue
        mid = (lo + hi) / 2
        i = min(searchsortedfirst(Q, mid), length(q))
        j = min(searchsortedfirst(R, mid), length(r))
        joint[i, j] += hi - lo
    end
    return joint
end

"""
    stochastic_pair(T1, T2; coupling=:independent) -> StochasticCA

A stochastic cellular automaton into the product of the codomains of `T1` and
`T2`, two stochastic automata with the same domain and group, whose two
components have the distributions of `T1` and `T2`. A research extension: in
a Markov category such a pair is not unique, and `coupling` chooses one. With
`:independent` the two components are drawn independently at each cell; with
`:shared` both come from one uniform draw (the comonotone coupling). On
CellularAutomataCore these are two layers drawing with different draw numbers,
or with the same one.
"""
function stochastic_pair(T1::StochasticCA, T2::StochasticCA; coupling::Symbol=:independent)
    coupling in (:independent, :shared) ||
        throw(ArgumentError("coupling must be :independent or :shared, got :$coupling"))
    G = _same_group("pairing stochastic cellular automata", T1, T2)
    T1.dom == T2.dom ||
        throw(DomainMismatchError("pairing stochastic cellular automata", T1.dom, T2.dom))
    U = union(T1.memory, T2.memory)
    i1, i2 = _positions(T1.memory, U), _positions(T2.memory, U)
    κ1, κ2 = T1.kernel, T2.kernel
    shared = coupling === :shared
    κ = function (y)
        q, r = κ1(Tuple(y[i] for i in i1)), κ2(Tuple(y[i] for i in i2))
        joint = shared ? _shared_coupling(q, r) : q * r'
        return vec(joint)  # first factor fastest, the order of the product alphabet
    end
    return StochasticCA(G, U, κ, T1.dom, _shift_product(T1.codom, T2.codom))
end

"""
    LocalRule(T::StochasticCA; draw=1)

A CellularAutomataCore rule that samples the stochastic cellular automaton `T`
(over a cyclic or torus group, with equal domain and codomain): each cell's new
state is drawn from its kernel by inverting the cumulative probabilities at
the counter-based uniform `uniform(ctx, draw)`. Rules that use the same `draw`
on different layers are coupled through it.
"""
function CAC.LocalRule(T::StochasticCA{<:Union{CyclicGroup,TorusGroup}}; draw::Integer=1)
    T.dom == T.codom ||
        throw(DomainMismatchError("a core rule from a stochastic cellular automaton", T.dom,
                                  T.codom))
    G = T.group
    e = identity_element(G)
    others = filter(!=(e), T.memory)
    offsets = isempty(others) ? [_offset(G, last(elements(G)))] :
              [_offset(G, s) for s in others]
    src = [s == e ? 0 : findfirst(==(s), others) for s in T.memory]
    values = alphabet(T.codom).values
    κ = T.kernel
    return CAC.LocalRule(CAC.Offsets(offsets)) do c, n, ctx
        q = κ(Tuple(k == 0 ? c : n[k] for k in src))
        u = CAC.uniform(ctx, draw)
        k = min(searchsortedfirst(cumsum(q), u), length(values))
        return values[k]
    end
end

function CAC.CAProblem(T::StochasticCA{<:Union{CyclicGroup,TorusGroup}}, u0, tspan, args...;
                       draw::Integer=1, kwargs...)
    u = u0 isa Configuration ? parent(u0) : u0
    return CAC.CAProblem(CAC.LocalRule(T; draw), u, tspan, args...;
                         space=torus_space(T.group), kwargs...)
end
