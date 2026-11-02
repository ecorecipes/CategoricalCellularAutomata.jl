# The exception hierarchy: every exception type this package defines, exported
# or not, subtypes the root `CategoricalCellularAutomataError`, and the types keep their module and their
# unqualified names.
function owned_exception_types(M)
    types = Type[]
    for n in names(M; all=true)
        isdefined(M, n) || continue
        T = getglobal(M, n)
        T isa Type && T <: Exception && parentmodule(T) === M && push!(types, T)
    end
    return types
end

@testset "errors" begin
    owned = owned_exception_types(CategoricalCellularAutomata)

    @testset "hierarchy" begin
        @test isabstracttype(CategoricalCellularAutomataError)
        @test CategoricalCellularAutomataError <: Exception
        # The search is not vacuous: it finds the root.
        @test CategoricalCellularAutomataError in owned
        for T in owned
            @test T <: CategoricalCellularAutomataError
            @test string(T) == string(nameof(T))
        end
    end
end
