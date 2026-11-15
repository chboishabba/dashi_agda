# 13 in 27: same-carrier antipodal quotient and diamond-axis restriction

## Reviewed primary repository PR donors (2026-10-26)
- PR #1249: `DASHI.Unified.Hyperfabric27MinusOneAntipodalSameCarrierCutExact` proves the sign inversion on the **original** path-graph cube, involutivity, unique fixed origin, adjacency-preservation, and reuses the two-sided 1+26 Albert-*shape* chart. The 13-pair cardinality is already sourced to `IbrahimA027907PathCubeTernaryExceptionalThirteenSnowballExact`; do not duplicate its owner or promote the set bijection to exceptional-Jordan multiplication.
- PR #1239: `JInvariant369Cube27ModularSliceActionExact` defines a specific mod-3 linear action on each nine-site xy slice, which is bijective but **not** a native nearest-neighbour cube-graph automorphism; `Base369AlbertF3CubeHamiltonianSymmetryMaxCutExact` distinguishes the nonperiodic path cube from C3³ torus translations and from Jordan/Monster actions.
- PR #1261: `DiamondTernary111AxisBridgeExact` and `DiamondNVFourAxisPermutationExact` encode eight signed corners and four unoriented body-diagonal axes, respectively.

## Exact refinement: not just four but thirteen axial classes

For X = {-1,0,1}³, coordinate negation has one fixed point 0 and
13 size-two orbits. The nonzero sign-support stratification is:

| nonzero coordinate count | number of points | antipodal pairs | directions |
| 1 | 6 | 3 | axial [100] families |
| 2 | 12 | 6 | face-diagonal [110] families |
| 3 | 8 | 4 | body-diagonal [111] families |

The total is 3+6+4=13. Thus the diamond <111> quotient is an
equivariant subcarrier of four elements inside the 13-class quotient,
not the entirety of it. The full cubic signed-permutation group B3
preserves all three support-size strata. The full action on the 13 projective axes has kernel {±I}, while the action on the 26 oriented nonzero sites is faithful (unlike the action on only four body
diagonals, whose kernel is {±I}).

## Three distinct uses of 13/111 (avoid a false equivalence)

1. Ordinary base-three numeral 111_3 evaluates to 13, as proved by
   `AllOnesPadicThresholdBoundary.allOnesPrefix3`.
2. With **ordinary base-three position digits** d in {0,1,2} and
   *centred coordinates* x=d-1, the linear 0..26 index 13
   (digits 111_3) corresponds to the origin (0,0,0), not the corner
   (+1,+1,+1). The latter has ordinary digits 222_3 and index 26.
3. With **balanced ternary signed digits** {-1,0,+1}, the string
   (+1,+1,+1) evaluates to integer 13, and is a corner [111].
   This is a different codec/evaluation map.
4. The *thirteen nonzero antipodal pairs* count is a quotient
   cardinality, not the number 13's position in an index scheme.

This is an important semantic distinction: a single surface form 111
may refer to the centre under one indexing convention and to an outer
corner under another. Preserve the codec tag and the residual.

## Mathematical and physical gates

- Direct reuse: import the PR #1249 original antipode and quotient
  once merged, rather than creating a second arbitrary antipode.
- Define a typed quotient orbit and support-count classifier with
  reconstructible orientation residual; certify 3+6+4 orbit strata.
- Prove B3 equivariance with the central ±I kernel on all 13 axes and restrict to the diamond
  four-axis subcarrier. For four body-diagonal axes the effective
  permutation group is S4 with central ±I kernel; for all thirteen
  axes the action is faithful because coordinate sign flips and
  permutations are distinguished on coordinate and diagonal lines.
- The native modular sheet map from PR #1239 generally does not
  preserve support-size stratification or nearest-neighbour
  adjacency: do not identify its order-four orbit with a spatial C4
  rotation without an equivariance proof.
- Diamond NV defect directions use only [111]-type orbits. Their
  physical site stabilisers and quantum Hamiltonian representations
  still need independently typed symmetry proofs.
- No equality between Albert algebra multiplication, Monster
  actions, bosonic-string dimensions, scalar 13, and physical
  crystal structure follows from the shared 27-site cardinality.

## Attribution
Classical cubic group actions/projective axes and base-three
arithmetic are prior art. Native formal proofs and computational
receipts remain attributed to their PR owners, including the 2026-10-24
PR #1249 and PR #1239 work. This document only cross-references
and adds the typed codec/stratification consequences; it does not
claim these PRs are merged or typechecked locally.

## 2026-10-26 actual latest-PR refresh: native punctured27 PG13 ↔ Albert26 C13

**New source discovery (not a new duplicate cube):** Agda crystallography #1261 has `Punctured27NineSheetBridgeExact`, `docs/crystallography_13_in_27_antipodal_diamond_crosspr_20261026.md`, and the existing 13-axis/B3 regression; hyperfabric #1249 ALREADY OWNS the original path-cube antipode/involution/path-edge action, and Ibrahim owns the 1+26/2×13 shape chart. The recent #1261 script was **not executable as first fetched**, because two `\\n` sequences occurred literally outside strings; fixed on #1261 with commit `88848b4e` before adding the directed projective-graph holonomy checks.

**True SAME underlying F3³ grade/projective carrier:** 26 native nonzero cube points `F3³\{0}` have 13 antipodal lines with orientation bit and support strata 3 [100]+6 [110]+4 [111]. A canonical first-nonzero-positive normalisation gives a reversible **26 ↔ (13×Bool) SET** chart. The original graph has 27v/54e; punctured graph 26v/48e; antipodal quotient **13v/24e** (12 edges support1↔2 + 12 edges support2↔3), DIFFERENT from `PG(2,3)` point-line incidence of **52 flags** on the same 13 points. The spatial quotient's edge-sign cocycle has a **four-edge odd XOR holonomy** `[100]→[110]→[010]→[1,-1,0]→[100]` with edge bits 0,0,1,0, so no globally edge-compatible oriented 13-site section. Independent exact local `/mnt/data/check_pg13_cube26_orientation_holonomy.py` PASS. Agda #1249 new `DASHI/Unified/HyperfabricPunctured27Projective13OrientationExact.agda` consumes the actual native antipode, with 26 source-written two-sided `refl` reductions, 26 antipode reductions, four ACTUAL native edge constructors and 16-case XOR no-section proof (**Agda kernel not run**). Existing #1261 graph regression corrected and extended in place.

**Strongest POSITIVE mathematical upgrade:** The selected Griess 1990 order13 automorphism on these 26 nonzero grades has **two genuine 13-cycles**. Its FREE Q-VECTOR SPACE has a two-cycle permutation matrix P. From the *ACTUAL* preexisting 26D traceless native rational Albert operator B, explicit 26×26 cyclic basis X = `[e0,Be0,...,B^12e0 | e1,Be1,...,B^12e1]` satisfies **B X = X P**, exact **det(X) = -729/4096 ≠ 0** (local independent SymPy PASS with intentional B-mutation rejection). Thus these are genuinely isomorphic as **Q[C13] modules**, not just equal dimensions; each 13D permutation module reduces to 1+12 over Q, so Albert J0 decomposes 2+12+12. It does NOT identify the finite 26-site SET with a Q26 VECTOR SPACE, spatial graph adjacency with Jordan multiplication, an actual Monster 3B VOA constituent, a physical bosonic string 26D target, or a different source actor. Lean #52 new `Integration/Griess1990Projective13PuncturedCube27SameGrade.lean` and `Integration/Griess1990Punctured27Albert26Order13Intertwiner.lean` import ACTUAL original Grade and previous B; finite Lean proofs source-written, **no Lean kernel run**. Standalone local exact checker `/mnt/data/check_griess1990_punctured27_albert26_C13_intertwiner.py` PASS against previous 26D rational JSON certificate.

**Sharp negative action discriminator:** same source-actor sends original P3³ edge `(0,0,0)~(0,1,0)` to `(0,0,0),(1,1,1)`, not adjacent; therefore the positive rational C13 module equivalence does not give a graph automorphism or original-Laplacian intertwiner. The older original T5 240 vs structured E8 Weyl fixed-root 13-no-go is separate and remains intact.

**Full focused Pareto/source ledger**: [Lean #52 2026-10-26 punctured27/PG13/Albert26](https://github.com/chboishabba/dashi_lean4/blob/agent/albert-jordan-f4-maxcut-20261007/docs/superpowers/plans/2026-10-26-griess-punctured27-projective13-albert26-equivariant-maxcut.md); [Agda #1261 crystal companion](https://github.com/chboishabba/dashi_agda/blob/feat/tetragonal-d4h-exact-20261025/docs/crystallography_punctured27_pg13_orientation_albert26_C13_maxcut_20261026.md). P0 kernel acceptance of original Griess source→native 729 Jordan product and C13/26 basis plus Agda actual antipoidal codec/holonomy. Source-original Griess Jr. 1990 DOI 10.1016/0021-8693(90)90176-O, classical PG2(3)/B3/Maschke, inherited Ibrahim A027907 Sloane/McGarvey/Foster/Riordan provenance, newer source donor PR #1261 crystal and PR #1249 graph, distinct Chen–Lam–Shimakura Monster Z3 VOA. **Do not collapse source, calculation, source-written proof, kernel receipt, empirical action or physical inference.**
