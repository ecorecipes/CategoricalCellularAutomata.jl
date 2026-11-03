# Gluing spaces: lattice patches glued along their faces must give the core's lattices (strips,
# cylinders, tori, blocks of patches, hexagonal ones) up to the order of cells, as maps of spaces
# that are bijective and preserve neighbours; a rule on the landscape restricted to a patch must be
# the rule on the patch reading its halo; and the union-find colimit must agree with Catlab's.

using Catlab: apex, legs, nparts, add_parts!, FinFunction

# The map from the closed landscape to a core lattice, by the coordinates of each patch's cells.
function landscape_map(landscape, inclusions, offsets, patch, nbhd, core; boundary=0)
    g = apex(landscape)
    S = NeighbourhoodSpace(g; boundary)
    rank = Dict(c => k for (k, c) in enumerate(interior_cells(g)))
    coords = patch_coordinates(patch, nbhd)
    lin = LinearIndices(size(core))
    bds = CellularAutomataCore.boundaries(core)
    image = zeros(Int, free_cells(S))
    for (ι, off) in zip(inclusions, offsets), c in 1:prod(size(patch))
        I = Tuple(coords[c]) .+ off
        I = ntuple(d -> bds[d] isa Periodic ? mod1(I[d], size(core)[d]) : I[d], length(I))
        k = rank[ι[c]]
        @assert image[k] in (0, lin[I...])
        image[k] = lin[I...]
    end
    return SpaceMorphism(S, neighbourhood_space(core, nbhd), image)
end
function is_iso(f)
    return is_morphism(f) && sort(f.map) == 1:free_cells(f.codom) &&
           free_cells(f.dom) == free_cells(f.codom)
end

# The two colimits agree up to the order of cells: the inclusions induce a bijection of cells
# that carries the slots of one onto the slots of the other.
function same_colimit(d, patches)
    (L1, ι1), (L2, ι2) = glue(d, patches), glue(d, patches; algorithm=:catlab)
    g1, g2 = apex(L1), apex(L2)
    nparts(g1, :Cell) == nparts(g2, :Cell) || return false
    σ = zeros(Int, nparts(g1, :Cell))
    for (a, b) in zip(ι1, ι2), (x, y) in zip(a, b)
        σ[x] in (0, y) || return false
        σ[x] = y
    end
    sort(σ) == 1:nparts(g2, :Cell) || return false
    slots(g, f) = sort([(f(g[s, :reader]), f(g[s, :read]), g[s, :index])
                        for s in 1:nparts(g, :Slot)])
    legs_agree = all(zip(legs(L1), legs(L2))) do (l1, l2)
        return σ[collect(l1[:Cell])] == collect(l2[:Cell])
    end
    return slots(g1, c -> σ[c]) == slots(g2, identity) && legs_agree
end

life(c, ns) = (s=sum(ns); s == 3 || (c == 1 && s == 2) ? 1 : 0)

@testset "slot graphs and patches" begin
    # closed spaces survive the round trip through slot graphs
    for space in (Torus(6, 5), HexGrid(5, 4), Grid(7, 4; boundary=Constant(1)),
                  GraphSpace([[2, 3], [1], [1, 2]]))
        S = neighbourhood_space(space)
        g = slot_graph(S)
        @test NeighbourhoodSpace(g; boundary=isempty(S.pinned) ? nothing : 1) == S
        @test length(halo_cells(g)) == length(S.pinned)
    end
    # a patch: its cells, then a halo of the reach of the neighbourhood; two faces per axis
    P = lattice_patch(Grid(5, 4), Moore(1))
    g = apex(P)
    @test nparts(g, :Cell) == 7 * 6 && nparts(g, :Slot) == 20 * 8
    @test interior_cells(g) == 1:20 && length(halo_cells(g)) == 22
    coords = patch_coordinates(Grid(5, 4), Moore(1))
    @test coords[1:20] == vec(collect(CartesianIndices((5, 4))))
    @test all(I -> I[1] in (0, 6) || I[2] in (0, 5), coords[21:end])
    @test length(legs(P)) == 4
    @test [length(collect(l[:Cell])) for l in legs(P)] == [12, 12, 14, 14]
    @test coords[collect(legs(P)[2][:Cell])] ==
          vec(collect(CartesianIndices((5:6, 0:5))))
    # a reach of 2 on one axis and 1 on the other
    Q = lattice_patch(Grid(6, 5), Offsets([(-2, 0), (2, 0), (0, -1), (0, 1)]))
    @test [length(collect(l[:Cell])) for l in legs(Q)] == [4 * 7, 4 * 7, 2 * 10, 2 * 10]
    # an open space needs a boundary value to close
    @test_throws ArgumentError NeighbourhoodSpace(g)
    S = NeighbourhoodSpace(g; boundary=0)
    @test free_cells(S) == 20 && collect(values(S.pinned)) == [0]
    # one step on a patch: interior cells update, halo cells keep their values
    x = rand(Xoshiro(2), 0:1, nparts(g, :Cell))
    y = apply_local(life, g, x)
    @test y[21:end] == x[21:end]
    x[21:end] .= 0                                 # the halo holding the boundary value
    @test apply_local(life, g, x)[1:20] == apply_local(life, S, x[1:20])
    @test_throws ArgumentError apply_local(life, g, x[1:5])
end

@testset "glued landscapes are the core's lattices" begin
    nb = Moore(1)
    patch = Grid(10, 8)
    P = lattice_patch(patch, nb)
    pair = @relation () begin
        P(w, s, x1, x2)
        P(s, e, y1, y2)
    end
    L, ι = glue(pair, Dict(:P => P))
    f = landscape_map(L, ι, [(0, 0), (10, 0)], patch, nb, Grid(20, 8; boundary=Constant(0)))
    @test is_iso(f)
    # the same along the second axis, with a NamedTuple of patches
    stack = @relation () begin
        P(a1, a2, w, s)
        P(b1, b2, s, e)
    end
    L, ι = glue(stack, (P=P,))
    @test is_iso(landscape_map(L, ι, [(0, 0), (0, 8)], patch, nb,
                               Grid(10, 16; boundary=Constant(0))))
    # a patch glued to itself: a cylinder (one axis) or a torus (both): coequalisers
    cylinder = @relation () begin
        P(x, x, a, b)
    end
    L, ι = glue(cylinder, Dict(:P => P))
    @test is_iso(landscape_map(L, ι, [(0, 0)], patch, nb,
                               Grid(10, 8; boundary=(Periodic(), Constant(0)))))
    torus = @relation () begin
        P(x, x, y, y)
    end
    L, ι = glue(torus, Dict(:P => P))
    @test isempty(halo_cells(apex(L)))
    @test is_iso(landscape_map(L, ι, [(0, 0)], patch, nb, Torus(10, 8)))
    # four patches in a block: corner cells are shared by four patches
    block = @relation () begin
        P(a1, m1, b1, n1)
        P(m1, c1, b2, n2)
        P(a2, m2, n1, d1)
        P(m2, c2, n2, d2)
    end
    L, ιb = glue(block, Dict(:P => P))
    @test is_iso(landscape_map(L, ιb, [(0, 0), (10, 0), (0, 8), (10, 8)], patch, nb,
                               Grid(20, 16; boundary=Constant(0))))
    # other neighbourhoods and shapes
    for (patch, nb, core, offsets, d) in
        ((Grid(6, 5), VonNeumann(1), Grid(12, 5; boundary=Constant(0)), [(0, 0), (6, 0)],
          pair),
         (Grid(6, 5), Moore(2), Grid(12, 5; boundary=Constant(0)), [(0, 0), (6, 0)], pair),
         (Grid(9), Moore(2), Grid(18; boundary=Constant(0)), [(0,), (9,)],
          @relation () begin
              P(w, s)
              P(s, e)
          end),
         (HexGrid(6, 5), Hexagonal(1), HexGrid(6, 5), [(0, 0)], torus),
         (HexGrid(6, 5), Hexagonal(1), HexGrid(12, 5; boundary=Constant(0)),
          [(0, 0), (6, 0)], pair))
        L, ι = glue(d, Dict(:P => lattice_patch(patch, nb)))
        @test is_iso(landscape_map(L, ι, offsets, patch, nb, core))
    end
    # glued again along the outer legs: two strips of two make a strip of four
    strip = @relation (w, e) begin
        P(w, s, x1, x2)
        P(s, e, y1, y2)
    end
    S2, ι2 = glue(strip, Dict(:P => P))
    @test length(legs(S2)) == 2
    twice = @relation () begin
        Q(x, y)
        Q(y, z)
    end
    L, ι4 = glue(twice, Dict(:Q => S2))
    inclusions = [ι4[q][ι2[p]] for q in 1:2 for p in 1:2]
    @test is_iso(landscape_map(L, inclusions, [(0, 0), (10, 0), (20, 0), (30, 0)], patch,
                               nb,
                               Grid(40, 8; boundary=Constant(0))))
end

@testset "local rules restrict to patches" begin
    patch = Grid(7, 6)
    P = lattice_patch(patch, Moore(1))
    block = @relation () begin
        P(a1, m1, b1, n1)
        P(m1, c1, b2, n2)
        P(a2, m2, n1, d1)
        P(m2, c2, n2, d2)
    end
    L, ι = glue(block, Dict(:P => P))
    g, gP = apex(L), apex(P)
    rng = Xoshiro(3)
    table = rand(rng, 0:2, 3^9)
    lookup(c, ns) = table[1 + c + 3 * foldl((a, v) -> 3a + v, ns; init=0) % 3^8]
    for f in (life, lookup), _ in 1:3
        x = rand(rng, 0:(f === life ? 1 : 2), nparts(g, :Cell))
        y = apply_local(f, g, x)
        for b in 1:4
            # a configuration on the landscape restricts to each patch (a pullback), and the
            # landscape's step restricted to the patch is the patch's step reading its halo
            yb = apply_local(f, gP, x[ι[b]])
            @test all(c -> yb[c] == y[ι[b][c]], interior_cells(gP))
        end
    end
    # the patches cover the landscape's interior cells, each exactly once
    owners = reduce(vcat, [ι[b][interior_cells(gP)] for b in 1:4])
    @test sort(owners) == interior_cells(g)
end

@testset "the union-find colimit is Catlab's" begin
    P = lattice_patch(Grid(4, 3), Moore(1))
    H = lattice_patch(HexGrid(4, 3), Hexagonal(1))
    strip = @relation (w, e) begin
        P(w, s, a, b)
        P(s, e, c, f)
    end
    torus = @relation () begin
        P(x, x, y, y)
    end
    mixed = @relation () begin
        P(a, x, b, c)
        H(x, f, g, h)
    end
    for (d, patches) in ((strip, Dict(:P => P)), (torus, Dict(:P => P)),
                         (mixed, Dict(:P => P, :H => H)))
        @test same_colimit(d, patches)
    end
end

@testset "a lattice joined to a network" begin
    # three fields in a row, each reading a road node; the road nodes read each other and
    # their field: a connector supplies the extra slots, numbered after the patches' own
    P = lattice_patch(Grid(3, 3), Moore(1))
    road = slot_graph(neighbourhood_space(GraphSpace([[2], [1, 3], [2]])))
    R = OpenSlotGraph{Int}(road, FinFunction([1, 2, 3], 3))
    cells = [patch_coordinates(Grid(3, 3), Moore(1))[c] for c in 1:9]
    centre = findfirst(==(CartesianIndex(2, 2)), cells)
    C = SlotGraph{Int}()
    add_parts!(C, :Cell, 6)                        # 1-3 field centres, 4-6 road nodes
    add_parts!(C, :Slot, 6; reader=[1, 2, 3, 4, 5, 6], read=[4, 5, 6, 1, 2, 3],
               index=[9, 9, 9, 2, 3, 2])
    connector = OpenSlotGraph{Int}(C, FinFunction([1], 6), FinFunction([2], 6),
                                   FinFunction([3], 6), FinFunction([4, 5, 6], 6))
    n = nparts(apex(P), :Cell)
    faces = [FinFunction(Vector{Int}(collect(l[:Cell])), n) for l in legs(P)]
    centre_leg = OpenSlotGraph{Int}(apex(P), faces..., FinFunction([centre], n))
    d = @relation () begin
        F(a1, m1, b1, c1, f1)
        F(m1, m2, b2, c2, f2)
        F(m2, a2, b3, c3, f3)
        Road(r)
        Link(f1, f2, f3, r)
    end
    L, ι = glue(d, Dict(:F => centre_leg, :Road => R, :Link => connector))
    S = NeighbourhoodSpace(apex(L); boundary=0)
    lengths = sort(length.(S.neighbours[1:free_cells(S)]))
    @test count(==(9), lengths) == 3 && count(==(8), lengths) == 24
    @test sort(filter(<(8), lengths)) == [2, 2, 3]
    # a field centre's ninth neighbour is its road node, which reads its field last
    rank = Dict(c => k for (k, c) in enumerate(interior_cells(apex(L))))
    for b in 1:3
        k = rank[ι[b][centre]]
        node = S.neighbours[k][9]
        @test S.neighbours[node][end] == k
    end
end

@testset "gluing errors" begin
    P = lattice_patch(Grid(5, 4), Moore(1))
    Q = lattice_patch(Grid(5, 3), Moore(1))
    # faces of different sizes
    side = @relation () begin
        P(a, s, b, c)
        Q(s, d, e, f)
    end
    @test_throws ArgumentError glue(side, Dict(:P => P, :Q => Q))
    # a box whose patch has a different number of legs, an unknown box, an unknown algorithm
    one_port = @relation () begin
        P(x)
    end
    @test_throws ArgumentError glue(one_port, Dict(:P => P))
    @test_throws ArgumentError glue(one_port, Dict(:Q => P))
    torus = @relation () begin
        P(x, x, y, y)
    end
    @test_throws ArgumentError glue(torus, Dict(:P => P); algorithm=:fast)
    # two patches that both update the same cells give them their slots twice
    overlap = @relation () begin
        P(x, a, b, c)
        P(x, d, e, f)
    end
    L, _ = glue(overlap, Dict(:P => P))
    @test_throws ArgumentError NeighbourhoodSpace(apex(L); boundary=0)
end
