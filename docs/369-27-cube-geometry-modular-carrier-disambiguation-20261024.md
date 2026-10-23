# Canonical DASHI 369 27-carrier disambiguation and geometrical modular max-cut

## User-established default geometry (do not reinterpret silently)
3 = one ternary line {-1,0,+1}. 6 = two compatibly glued ternary lines. 9 = an actual 3×3 sheet, including (0,0). 18 = two compatibly glued nine-position sheets. 27 = one actual 3×3×3 spatial balanced-ternary cube. The C3 three strands are three moving entities; 12 is the number of time samples. No number here automatically denotes the dimension of a Hilbert space or a Monster representation.

Canonical owner: DASHI/Foundations/Base369Ternary27HypervoxelFabricGeometryExact.agda defines Ternary27Point with literal x/y/z SSP trits; origin; six outer faces; HypervoxelAdjacent (a real one-coordinate ±1 grid step); cube and appraisal products. A 3×3×3 cube has 27 positions, 54 undirected grid edges, 8 corners (degree 3), 12 edge-middle sites (degree 4), 6 face centres (degree 5), and 1 central site (degree 6). The 27^3 hyperfabric (19683 states) is **three independent cubes**, not one 27-cube.

Other existing verified owners: DASHI/Moonshine/JInvariant369CodecBidiExact.agda (same-point, lossless actual Cube27 finite codec); DASHI/Moonshine/JInvariant369CodecPantsFrameBidiExact.agda (third cube coordinate matches third pants/refinement slot for that consumer); DASHI/Governance/HyperformalTernary27GeometryBridgeExact.agda (epistemic 9 -> three cubes); DASHI/Reasoning/Trialectic369RubikRefinementExact.agda (finite cube to 3 trits/depth address, not intrinsic dynamics). Do not re-invent the cube.

## What earlier work incorrectly blurred
1. A **spatial Cube27** has underlying set (SSPTrit)^3, adjacency, axis/face geometry.
2. A **principal-level modular residue** at depth3 is Z/27Z, with +1 carry and T cusp translation. It is an abstract 27-element cyclic additive group. The full SL2(Z/27) action of the braid acts on **pairs** of such residues, yielding 729 coordinate pairs; this 729 is not the 27 geometric cube or the 27^2 appraisal fibre by default.
3. A **Monster element of order27** is an element g satisfying ord(g)=27. Its cyclic powers have 27 labels, and twisted-twining sector label pairs (g^r,g^s) have 729 distinct formal ordered pairs; actual VOA trace equality may identify some. Nothing canonically gives those powers cube adjacency.
4. **Cube27's set bijection with residue digits** can be chosen, because both sets have 27 elements. It does not transfer the cube grid graph, physically interpreted coordinate roles, a modular curve, a Monster representation, or full braid isotopy.

## New exact Agda geometry-to-residue CHART bridge
DASHI/Moonshine/JInvariant369Cube27CuspCodecNonIsometryExact.agda imports the actual Ternary27Point and existing 3-trit residue carrier. It defines separately tagged SpatialCube27 and PrincipalCusp27, proves explicit inverse digit-code roundtrips, and exhibits the killer difference: the native cube's +++ corner has signed-digit code +13; adding 1 in cyclic Z/27 wraps to --- with signed code -13. Those two corners are not adjacent by the native cube graph. Therefore the chosen codec is a bijection but not an adjacency intertwiner.

An INTRINSIC theorem strengthens this example: the 3×3×3 nearest-neighbour cube graph is bipartite (parity of nonzero coordinates flips on each edge), with parts of size 13 and 14. It has no odd cycles. A Z/27 +1 action is a single 27-cycle, so **no** bijection can make *all* successive cyclic +1 steps into cube grid edges, regardless of selected digit encoding. This obstruction is established by parity and checked over all 54 edges in the Python fixture.

## New actual Cube27 modular cut (not just residue27)
DASHI/Moonshine/JInvariant369Cube27ModularSliceActionExact.agda imports the existing F3^2 punctured nine-sheet modular matrix. After selecting z as the three-sheet index, it acts on each *real cube* sheet by M(x,y,z)=(x+y,x-y,z) mod3. Source-written lemmas state that this commutes with the preexisting 9-sheet M action, preserves z, squares to (−x,−y,z), and has fourth power identity. It is a permutation of the 27 actual cube sites, with **three fixed points** (0,0,z) and **six four-cycles**, NOT a C27 translation or spatial Euclidean rotation.
Crucial no-isometry witness: the genuine cube edge (0,0,0)->(1,0,0) is sent to (0,0,0)->(1,1,0), which is *not* an edge. Thus this exact coordinate action cannot be promoted to a physical cube-graph symmetry or spatial rotation without a changed adjacency/metric and a new proof.

## Runtime checks
scripts/check_369_cube27_geometry_vs_modular_charge.py exhaustively tests 27 sites, all 54 grid edges and degree distributions, the cube/residue inverse digit chart and carry corner wrap, full 27-site M orbit structure, the adjacency counterexample, and intrinsic bipartite impossibility of a 27-cycle graph walk. Equivalent independent local Python enumerations PASS.

## Physical test preservation
Retain Monster 27A/27B and B3 modular phase as *distinct typed consumers*. To detect a physical 3D cube geometry, an experiment must supply a geometric observable (adjacency, spatial orientation, metric or 3D transport); an order-27 Monster twisted trace tests the **cyclic group action** on CFT states, not cube geometry. To connect them, provide a geometric cube -> marked torus/VOA twist representation that preserves the specified operator/connection, plus an actual observable comparing corresponding histories. No same-object witness exists yet.

## Acceptance and truthful verification
python3 scripts/check_369_cube27_geometry_vs_modular_charge.py
agda -i . -i /path/to/agda-stdlib DASHI/Moonshine/JInvariant369Cube27CuspCodecNonIsometryExact.agda
agda -i . -i /path/to/agda-stdlib DASHI/Moonshine/JInvariant369Cube27ModularSliceActionExact.agda
Python independent enumeration of the finite identities passed. Both Agda modules are source-written/committed, NOT Agda-kernel certified on this head. The geometric nonisometry/no-odd-cycle argument is mathematical, not a full KK, Monster/AdS3, or physical braid correspondence.