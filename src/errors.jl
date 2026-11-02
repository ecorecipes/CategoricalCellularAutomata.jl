# Exceptions of CategoricalCellularAutomata. Every exception the package defines lives in this
# file, with its `showerror` method, and subtypes the root `CategoricalCellularAutomataError`.
#
# - Carry the offending names (layer, rule, backend, model) in the fields and the message.
#   Library code never calls a bare `error("...")`.
# - Invalid arguments and keywords raise `ArgumentError`, not a type from this file.
# - A docstring names another package's type as a code span, never with `@ref`.

"""
    CategoricalCellularAutomataError

Abstract supertype of every exception that CategoricalCellularAutomata defines. It marks the
package that introduced an error, not a kind of failure. Invalid arguments and
keywords raise Base's `ArgumentError` instead, which is outside this root.
"""
abstract type CategoricalCellularAutomataError <: Exception end

"""
    GroupMismatchError(operation, G, H)

Raised when an operation combines cellular automata, configurations or full
shifts over different groups `G` and `H`: the category of cellular automata
over a group only composes and pairs automata over that group.
"""
struct GroupMismatchError <: CategoricalCellularAutomataError
    operation::String
    G::Any
    H::Any
end
function Base.showerror(io::IO, e::GroupMismatchError)
    return print(io, "GroupMismatchError: ", e.operation, " needs one group, got ", e.G,
                 " and ", e.H)
end

"""
    DomainMismatchError(operation, expected, got)

Raised when the codomain of a cellular automaton is not the domain of the next
one in a composite, or a configuration is not in the domain of the automaton it
is given to.
"""
struct DomainMismatchError <: CategoricalCellularAutomataError
    operation::String
    expected::Any
    got::Any
end
function Base.showerror(io::IO, e::DomainMismatchError)
    return print(io, "DomainMismatchError: ", e.operation, " expected ", e.expected,
                 ", got ",
                 e.got)
end

"""
    LayerConflictError(layer, boxes)

Raised when composing models with a wiring diagram would let more than one box
update the same layer: each shared layer has at most one owner, and the other
boxes on it must declare it as read only.
"""
struct LayerConflictError <: CategoricalCellularAutomataError
    layer::Symbol
    boxes::Vector{Symbol}
end
function Base.showerror(io::IO, e::LayerConflictError)
    return print(io, "LayerConflictError: layer ", e.layer, " would be updated by ",
                 join(e.boxes, " and "), "; declare it in `reads` for all but one of them")
end
