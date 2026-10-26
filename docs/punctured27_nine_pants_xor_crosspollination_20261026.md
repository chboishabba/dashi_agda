# Punctured 27, punctured nine, pants gluing and XOR-grid audit

## Same-carrier result
Let T={-1,0,1}. The existing owner for spatial T³ is
`DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact`.
Its puncture X*=T³\{(0,0,0)} contains 26 points.

Slice by the z coordinate:
- z=0: punctured nine-plane T²\{0}, eight points, already typed as
  `OggSSPP2BalancedTernaryPuncturedPlaneExact.PuncturedNineSheet`.
- z=-1 and z=+1: each the **complete** nine-plane, nine points.
Hence 26=8+9+9, *not* 3*8. Puncturing each of the three
planes removes three points and gives 24, a different construction.

The PR #1261 module
`DASHI.Mathematics.Symmetry.Punctured27NineSheetBridgeExact`
provides the 26-element sum presentation and forward map into the
native cube. The converse and genuine equivalence proof are still
open, pending a no-origin refinement/proof carrier.

## Two complementary quotients

1. Puncturing: X*=T³\{0}, 26 oriented nonzero points.
2. Antipodal sign quotient: X*/±, 13 unoriented point-directions,
   split into support-size orbits 3+6+4 under cubic signed-permutation
   symmetry. The source implementation of the involution and
   adjacency-preservation is PR #1249, not this PR.

Each of the two nonzero z-slice centres, (0,0,±1), are an antipodal
pair *across* sheets; the eight central plane points yield four
pairs *within* the middle slice. The other pairs require cross-sheet
identification, so one cannot quotient each slice independently and
expect the same seam data.

## Pants interface and gluing

`TypedHyperfabricPantsGluingBridgeExact` requires explicit
`Pants.InterfaceMatch` on two realized edge-stalk channels, with
matching proposition type, boundary capacity and phase.
It explicitly does *not* glue arbitrary stalks automatically.
`JInvariantColourWheelNineSheetPantsGluingExact` already owns
ternary slot/nine-sheet round trips and seam models.

For punctured 27, a correct pants/fibre interface consists of
three z-sheets and their vertical adjacency incidence. The middle
sheet has a missing central vertex; outer sheet centres exist.
To construct a compatible global section, retain typed seam
incidence, restrictions and orientation/provenance, and prove the
new restrictions satisfy the hyperfabric's compatibility equations.
Pants terminology alone is not a homeomorphism between a
three-dimensional punctured cube and a two-dimensional pair of
pants.

## XOR grid / signed gauge boundary

Found `NSTriadSignedXORGaugeabilityBoundary`:
its XOR is **mod-2** sign/gaugeability, and it expressly separates
balance from satisfiable gauge assignments, with the weighted
distance to im(B₂) unresolved. It is *not* an implementation of
the additive trit group C3³. There is a legitimate coupling:

- a ±1 orientation-residual on each antipodal pair gives a
  two-state sign chart, locally modelled by Z/2;
- glueing signs along graph edges introduces XOR transition bits;
- consistent global orientation choices exist iff XOR holonomy
  around every cycle vanishes (for a connected graph);
- inconsistent holonomy is a Z/2 1-cocycle/gauge obstruction
  relative to the chosen graph, not an automatic crystalline
  chirality or physical magnetic frustration theorem.

This coupling needs actual incidence, cochain and cycle proofs,
not a Boolean summary flag. It must never conflate the
27-state ternary position carrier and the binary sign fibre.

## Natural next proof obligations
- Bidirectional equivalence of the punctured 27 sum chart
  and the original origin-excluded native cube.
- Antipodal quotient compatibility with the three-sheet
  decomposition, including cross-sheet pairs.
- Hyperfabric `GlobalSection` and source's `InterfaceMatch`
  for real vertical seams.
- A Z/2 sign-fibre XOR cocycle and exact no-holonomy ↔
  global-orientation equivalence.
- Restrict the cubic W(B3) action to the four diamond
  body-diagonal classes, preserving source provenance.

## Source attribution boundaries
Native cube/antipode from PR #1249, punctured nine and
nine-sheet pants from their original named modules, and the NS XOR
gauge wall from `NSTriadSignedXORGaugeabilityBoundary`.
The new contribution is only this cross-owner analysis and
one source-level forward chart, not a proved sheaf equivalence,
full pants cobordism or physical diamond material model.
