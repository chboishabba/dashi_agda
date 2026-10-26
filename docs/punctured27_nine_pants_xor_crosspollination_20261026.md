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

## 2026-10-26 actual latest-PR refresh: native punctured27 PG13 ↔ Albert26 C13

**New source discovery (not a new duplicate cube):** Agda crystallography #1261 has `Punctured27NineSheetBridgeExact`, `docs/crystallography_13_in_27_antipodal_diamond_crosspr_20261026.md`, and the existing 13-axis/B3 regression; hyperfabric #1249 ALREADY OWNS the original path-cube antipode/involution/path-edge action, and Ibrahim owns the 1+26/2×13 shape chart. The recent #1261 script was **not executable as first fetched**, because two `\\n` sequences occurred literally outside strings; fixed on #1261 with commit `88848b4e` before adding the directed projective-graph holonomy checks.

**True SAME underlying F3³ grade/projective carrier:** 26 native nonzero cube points `F3³\{0}` have 13 antipodal lines with orientation bit and support strata 3 [100]+6 [110]+4 [111]. A canonical first-nonzero-positive normalisation gives a reversible **26 ↔ (13×Bool) SET** chart. The original graph has 27v/54e; punctured graph 26v/48e; antipodal quotient **13v/24e** (12 edges support1↔2 + 12 edges support2↔3), DIFFERENT from `PG(2,3)` point-line incidence of **52 flags** on the same 13 points. The spatial quotient's edge-sign cocycle has a **four-edge odd XOR holonomy** `[100]→[110]→[010]→[1,-1,0]→[100]` with edge bits 0,0,1,0, so no globally edge-compatible oriented 13-site section. Independent exact local `/mnt/data/check_pg13_cube26_orientation_holonomy.py` PASS. Agda #1249 new `DASHI/Unified/HyperfabricPunctured27Projective13OrientationExact.agda` consumes the actual native antipode, with 26 source-written two-sided `refl` reductions, 26 antipode reductions, four ACTUAL native edge constructors and 16-case XOR no-section proof (**Agda kernel not run**). Existing #1261 graph regression corrected and extended in place.

**Strongest POSITIVE mathematical upgrade:** The selected Griess 1990 order13 automorphism on these 26 nonzero grades has **two genuine 13-cycles**. Its FREE Q-VECTOR SPACE has a two-cycle permutation matrix P. From the *ACTUAL* preexisting 26D traceless native rational Albert operator B, explicit 26×26 cyclic basis X = `[e0,Be0,...,B^12e0 | e1,Be1,...,B^12e1]` satisfies **B X = X P**, exact **det(X) = -729/4096 ≠ 0** (local independent SymPy PASS with intentional B-mutation rejection). Thus these are genuinely isomorphic as **Q[C13] modules**, not just equal dimensions; each 13D permutation module reduces to 1+12 over Q, so Albert J0 decomposes 2+12+12. It does NOT identify the finite 26-site SET with a Q26 VECTOR SPACE, spatial graph adjacency with Jordan multiplication, an actual Monster 3B VOA constituent, a physical bosonic string 26D target, or a different source actor. Lean #52 new `Integration/Griess1990Projective13PuncturedCube27SameGrade.lean` and `Integration/Griess1990Punctured27Albert26Order13Intertwiner.lean` import ACTUAL original Grade and previous B; finite Lean proofs source-written, **no Lean kernel run**. Standalone local exact checker `/mnt/data/check_griess1990_punctured27_albert26_C13_intertwiner.py` PASS against previous 26D rational JSON certificate.

**Sharp negative action discriminator:** same source-actor sends original P3³ edge `(0,0,0)~(0,1,0)` to `(0,0,0),(1,1,1)`, not adjacent; therefore the positive rational C13 module equivalence does not give a graph automorphism or original-Laplacian intertwiner. The older original T5 240 vs structured E8 Weyl fixed-root 13-no-go is separate and remains intact.

**Full focused Pareto/source ledger**: [Lean #52 2026-10-26 punctured27/PG13/Albert26](https://github.com/chboishabba/dashi_lean4/blob/agent/albert-jordan-f4-maxcut-20261007/docs/superpowers/plans/2026-10-26-griess-punctured27-projective13-albert26-equivariant-maxcut.md); [Agda #1261 crystal companion](https://github.com/chboishabba/dashi_agda/blob/feat/tetragonal-d4h-exact-20261025/docs/crystallography_punctured27_pg13_orientation_albert26_C13_maxcut_20261026.md). P0 kernel acceptance of original Griess source→native 729 Jordan product and C13/26 basis plus Agda actual antipoidal codec/holonomy. Source-original Griess Jr. 1990 DOI 10.1016/0021-8693(90)90176-O, classical PG2(3)/B3/Maschke, inherited Ibrahim A027907 Sloane/McGarvey/Foster/Riordan provenance, newer source donor PR #1261 crystal and PR #1249 graph, distinct Chen–Lam–Shimakura Monster Z3 VOA. **Do not collapse source, calculation, source-written proof, kernel receipt, empirical action or physical inference.**
