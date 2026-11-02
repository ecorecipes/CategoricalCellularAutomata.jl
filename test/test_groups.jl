# Group axioms checked exhaustively on every kind of group, and configurations as a group action.

function check_group_axioms(G)
    E = collect(elements(G))
    e = identity_element(G)
    for g in E
        mul(G, e, g) == g == mul(G, g, e) || return false
        mul(G, g, inverse(G, g)) == e == mul(G, inverse(G, g), g) || return false
        for h in E, k in E
            mul(G, mul(G, g, h), k) == mul(G, g, mul(G, h, k)) || return false
        end
    end
    return all(g -> mul(G, E[1], g) in E, E)
end

const PERMS3 = [[1, 2, 3], [2, 1, 3], [1, 3, 2], [3, 2, 1], [2, 3, 1], [3, 1, 2]]

@testset "groups" begin
    S3 = FiniteGroup(PERMS3, (a, b) -> a[b])
    for G in (CyclicGroup(1), CyclicGroup(7), TorusGroup(3, 4), TorusGroup(2, 2, 3), S3)
        @test check_group_axioms(G)
        @test length(G) == length(elements(G)) == prod(shape(G))
    end
    @test elements(TorusGroup(2, 3))[2] == (1, 0)  # first axis fastest, as arrays
    @test mul(TorusGroup(4, 3), (3, 1), (2, 2)) == (1, 0)
    @test label(S3, mul(S3, 2, 3)) == PERMS3[2][PERMS3[3]]
    @test mul(S3, 2, 3) != mul(S3, 3, 2)
    @test S3 == FiniteGroup(S3.table) && hash(S3) == hash(FiniteGroup(S3.table))
    @test sprint(show, CyclicGroup(5)) == "CyclicGroup(5)"
    @test sprint(show, TorusGroup(4, 3)) == "TorusGroup(4, 3)"
    @test sprint(show, S3) == "FiniteGroup of order 6"

    @test_throws ArgumentError CyclicGroup(0)
    @test_throws ArgumentError TorusGroup(3, 0)
    @test_throws ArgumentError FiniteGroup([1 2; 2 2])        # not a group
    @test_throws ArgumentError FiniteGroup([1 2 3; 2 3 1])    # not square
    @test_throws ArgumentError FiniteGroup([1 3; 2 1])        # entries outside 1:n
    @test_throws ArgumentError FiniteGroup([[1, 2], [2, 1]], (a, b) -> [1, 1])  # not closed
    # a Latin square with an identity that is not associative
    loop = [1 2 3 4 5; 2 1 4 5 3; 3 5 1 2 4; 4 3 5 1 2; 5 4 2 3 1]
    @test_throws ArgumentError FiniteGroup(loop)

    @testset "configurations" begin
        G = TorusGroup(3, 4)
        x = Configuration(g -> g[1] + 10g[2], G)
        @test parent(x) == [i - 1 + 10(j - 1) for i in 1:3, j in 1:4]
        @test x[(2, 3)] == 32 && group(x) == G
        @test restrict(x, [(0, 0), (2, 3)]) == (0, 32)
        # shifting is a left action: g·(h·x) = (gh)·x, and e·x = x
        for g in elements(G), h in elements(G)
            @test shift(shift(x, h), g) == shift(x, mul(G, g, h))
        end
        @test shift(x, identity_element(G)) == x
        # and the same on a non-abelian group
        S3 = FiniteGroup(PERMS3, (a, b) -> a[b])
        y = Configuration(S3, collect(1:6) .* 7)
        @test all(shift(shift(y, h), g) == shift(y, mul(S3, g, h))
                  for g in elements(S3), h in elements(S3))
        @test_throws ArgumentError Configuration(G, zeros(4, 3))
        @test_throws ArgumentError shift(x, (5, 0))
        @test FinAlphabet(0:1) == FinAlphabet([0, 1]) && 1 in FinAlphabet(0:1)
        @test_throws ArgumentError FinAlphabet([1, 1])
    end
end
