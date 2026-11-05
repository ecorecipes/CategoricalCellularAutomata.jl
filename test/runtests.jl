using Test
using Random
using CategoricalCellularAutomata
using CellularAutomataCore
using Catlab: @present, @program, @relation, FreeCartesianCategory

@testset "CategoricalCellularAutomata" begin
    include("test_groups.jl")
    include("test_cartesian.jl")
    include("test_chl_bridge.jl")
    include("test_generalized.jl")
    include("test_markov.jl")
    include("test_spaces.jl")
    include("test_gluing.jl")
    include("test_model_maps.jl")
    include("test_errors.jl")
    include("test_docstrings.jl")
end
