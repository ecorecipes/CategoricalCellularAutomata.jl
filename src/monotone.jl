# Monotone cellular automata: alphabets that are partially ordered sets, and local rules that preserve
# the order, are the cellular automata of the category of posets. With configurations ordered cell by
# cell, such an automaton maps x ≤ y to τ(x) ≤ τ(y).

"""
    is_monotone(τ; leq=(<=), codom_leq=leq) -> Bool

Whether the local rule of the cellular automaton `τ` is monotone for the order
`leq` on its alphabet (and `codom_leq` on its codomain's): raising the state of
any cell of the memory set never lowers the result. It is checked one cell at a
time, which suffices for the product order on patterns. A monotone automaton
preserves the cellwise order of configurations, so runs started from ordered
initial configurations stay ordered.
"""
function is_monotone(τ::CellularAutomaton; leq=(<=), codom_leq=leq)
    A = alphabet(τ.dom)
    n = length(τ.memory)
    for p in _patterns(A, n, "is_monotone")
        v = τ.rule(p)
        for i in 1:n, a in A.values
            (a != p[i] && leq(p[i], a)) || continue
            codom_leq(v, τ.rule(Base.setindex(p, a, i))) || return false
        end
    end
    return true
end
