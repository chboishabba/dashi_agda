# 2026-10-26 same-grade max-cut: punctured27/PG13, signed graph, and actual Albert26 C13 module

## Original problem and recovery of prior work
The project began with the source-dependent Griess (1990) Albert triality coefficient residual **883/8 close to 888/8**. That raw comparison was basis-dependent; a noncanonical 60° plane rotation makes 888/8, while a genuine source-compatible rational related triple makes the correctly Gram-weighted residual exactly **zero** in independent finite algebra (original Lean #52 programme, not currently kernel-certified). Do not change the original objective into generic 369/Monster/physics numerology.

On 26 October the user specifically recalled recent **13 and 26 as punctured 27**. The relevant pre-existing SOURCE OWNERS were present and must not be duplicated:
- [Agda #1249](https://github.com/chboishabba/dashi_agda/pull/1249) `Hyperfabric27MinusOneAntipodalSameCarrierCutExact`: ACTUAL original nonwrapping `P3^3` cube, its antipode, involution, uniquely fixed origin and path-edge preservation. It also imports the earlier Ibrahim 1+26 *set* chart.
- [Agda #1261](https://github.com/chboishabba/dashi_agda/pull/1261) `Punctured27NineSheetBridgeExact` and original crystal/Diamond `111` modules: 26 **nonorigin sites** = 9+8+9, only the middle nine sheet punctured; exact four [111] diamond body-diagonal axes and original 13=3+6+4 orbit strata.
- [Agda #1239](https://github.com/chboishabba/dashi_agda/pull/1239): native ternary grades, Ibrahim/Griess Moufang M81 and source-modular/VOA C3 work; requires genuine same-action witness.
- [Lean #52](https://github.com/chboishabba/dashi_lean4/pull/52): Griess 1990 source phase g, real rational Albert 27D, order13 true source automorphism and its native TRACEZERO 26D linear operator B. Crucially this is not a finite 26-point set.
- [Lean #47](https://github.com/chboishabba/dashi_lean4/pull/47) and Agda #1098: structured E8 root240 and old T5 (243→240) separate, with previous no-go for fixed E8 Weyl root same-action; unaffected here.

## P0: actual SAME grade 13 points, retain orientation
The original cube coordinates are centered trits `{-1,0,+1}^3≅F3^3`, and Griess's original grading group is the SAME underlying F3³. Remove only zero: there are 26 nonzero grades, partitioned by scalar −1 into 13 projective lines of PG(2,3). The source codec retains an orientation residual:
```
F3³ \ {0} ≅ PG(2,3) points × {±1},     26 = 13×2.
```
Choose each representative by its FIRST nonzero coordinate being +1. This is an exact two-sided grade/point codec with signed inversion flipping the bit. It is **NOT** a bijection of one set of 26 points to the infinitely many elements of a Q-vector space of dimension26.

The cubic (W(B3)) signed-coordinate-permutation subgroup partitions 13 axes by support 3 [100] + 6 [110] + 4 [111]. All 48 cubic symmetries preserve nonwrapping graph edges and act on 13 projective axes with central kernel {±I}, effective order24; retaining the sign bit makes the action faithful on 26 signed sites. The Griess SL3(3) normalizer acts transitively on all projective lines, but does not preserve the spatial support partition or open edges. Base-three position number `111₃=13` corresponds to the center index 13 under 0..2 centered digit encoding, whereas balanced `+++ = 13` is the corner; these are different codecs.

**New implementation** on original antipode-owning Agda #1249:
`DASHI.Unified.HyperfabricPunctured27Projective13OrientationExact` imports the actual `Native.antipode` (does NOT duplicate it), defines all 13 actual canonical axes and their 3+6+4 support strata, `encode : Cube27→Maybe(Axis13×Bool)` with `nothing` at the original origin, `decode`, 26 `refl` encode/decode cases, all 27 source constructor cases for conditional converse and sign equivariance. New proof source only, Agda kernel UNCHECKED.

## P0: actual original QUOTIENT graph has Z2 holonomy; not PG incidence
Original nonwrapping `P3^3`: 27 vertices, 54 unoriented edges. Delete only global origin: 26 vertices, 48 edges. Quotient the PUNCTURED graph under native antipodal involution: **13 projective-axis vertices, 24 edges**, decomposed into 12 [100]↔[110] and 12 [110]↔[111]. The 13-axis graph degrees are 4 on nine [100]/[110] vertices and 3 on four [111] vertices.

On the SAME 13 underlying projective labels, **classical PG(2,3) point-line incidence** has 13 points, 13 dual hyperplanes, 52 incidence flags, four dual hyperplanes through each point. Its relation is NOT the above 24-edge spatial quotient graph and not a Jordan multiplication tensor.

For any quotient spatial edge a--b, selected canonical orientation representatives may be adjacent directly (bit ε=0) or only after flipping b (ε=1). The real four-cycle
```
[100] → [110] → [010] → [1 -1 0] → [100]
```
has edge bits **0,0,1,0**, XOR sum=1. Thus one traversal lifts from +[100] to −[100]. **No globally edge-compatible orientation section exists**, despite the 26↔13×2 TWO-SIDED SET chart. That is a genuine finite Z2 graph-cover holonomy discriminator relevant to the earlier pants/interface/XOR owners. It is NOT physical magnetic flux, a ternary C3³ phase, a nontrivial sheaf theorem, or a crystal specimen observation.

New actual Agda #1249 owner includes four NATIVE `Cube.HypervoxelAdjacent` edge witnesses and a 16-Boolean-case `noEdgeCompatibleOrientation` proof target (source-written, uncompiled). Independent exact local `check_pg13_cube26_orientation_holonomy.py` PASS. Existing crystal PR #1261 `scripts/check_crystal_27_13_b3_residual.py` originally had two literal backslash-n source syntax errors; corrected on its owning branch, and extended IN PLACE with exact 48→24 edge quotient and four-cycle XOR obstruction. Latest GitHub bytes were not executed in local Python; a separate independent local source-equivalent verifier was executed.

## P0: highest-information POSITIVE linear representation, not graph/Jordan identification
The source-corrected **actual Griess order13 action** (shears e01,e12,e20) acts on the 26 nonzero grades with TWO genuine 13-cycles (orbits based at (0,0,1) and (0,0,2)). Let P be the induced permutation matrix on the FREE Q-VECTOR SPACE ON THESE 26 POINT LABELS. Let B be the previously computed actual `RationalAlbertNative` tracezero26 rational order13 operator; this is NOT a site permutation.

From the same ORIGINAL B certificate, form the **literal 26×26 Q matrix**
```
X = [e0, Be0, ..., B^12e0 | e1, Be1, ..., B^12e1].
```
Independent exact SymPy computed and **PASS**:
```
B X = X P
det(X) = -729/4096 != 0
B^13 = P^13 = I
```
and a deliberate one-coefficient corruption of B destroys the equality. Hence the free rational grade26 permutation module and ACTUAL Albert J0^26 are genuinely ISOMORPHIC as **Q[C13] modules**. Characteristic polynomial on both sides:
`(T^13-1)^2=(T-1)^2 Φ13(T)^2`; two 13D **REDUCIBLE permutation modules** each decompose over Q into one fixed line and one irreducible 12D cyclotomic module, yielding **2+12+12**, NOT two irreducible 13D modules.

New Lean #52 `Integration/Griess1990Punctured27Albert26Order13Intertwiner.lean` REUSES the native J0 operator and original Grade, builds the exact two selected source-grade orbits, source permutation P, cyclic-basis X, finite BX=XP and determinant targets, plus source-actor NON-DESCENT on spatial P3 edges. All source-written Lean proof targets **NOT kernel checked**. Exact locally executed `check_griess1990_punctured27_albert26_C13_intertwiner.py` PASS, inputs `griess1990_order13_traceless26_certificate.json`; independent rational matrix certificate `griess1990_albert26_punctured27_two13cycles_intertwiner.json`. Standalone checker committed on Lean #52; committed byte-for-byte execution not established.

## P0: same-actor negative discriminator remains
The same valid Griess/Jordan order13 grade actor maps the original cube edge
`(0,0,0)~(0,1,0)` to `(0,0,0)` and `(1,1,1)`, which are **NOT** adjacent in P3³. This is a decisive counterexample to promoting the positive Q[C13] intertwiner to original spatial graph adjacency or Laplacian equivariance. Source-written Lean #52 `Griess1990Projective13PuncturedCube27SameGrade.lean` directly consumes the OLD `Grade`, true corrected actor and exact nonwrapping path relation, not a new idealised C13 toy. The old 240→E8 fixed-Weyl SAME-ACTION prime13 no-go remains separately valid.

## Pareto / Ibrahim / snowball remainder
- **P0 positive computationally CLOSED**: actual same-source 13×2 oriented grade codec; original punctured graph quotient/odd XOR cover; exact Q[C13]-linear 26D Albert intertwiner BX=XP.
- **P0 formal OPEN**: Lean kernel acceptance of source Griess original Q(ω) formula→729 rational Jordan products, actual order13 automorphism, new 26×26 cyclic basis determinant; Agda kernel typechecking of 26-site codec/16-case holonomy and original source-native transport. Neither Agda nor Lean toolchains available. No CI/kernel success claimed.
- **P1**: promote only legitimate action intertwiners to actual source/physical consumers. Spatial punctured cube is NOT path-adjacency invariant as a closed sector (native Agda #1249 previous no-go); retain the missing site and seam residual. The 26D traceless Albert space is not a graph site set, nor a bosonic string target, nor a Monster-VOA sector.
- **P2**: selected Monster 3B actual VOA mode and F4 full original-Q classification require independent source and operator payment; original 883/888 question already answered noncanonically.
- **Stop repeated numeric matches**: the structural acceptance basis is native sources, explicit operators, counterexamples, reproducible independent finite tests, **then** kernel receipts and scientific evidence.

## Attribution and source roles
Robert L. Griess Jr. (1990), *A Moufang loop, the exceptional Jordan algebra, and a cubic form in 27 variables*, J. Algebra 131:281–293, DOI `10.1016/0021-8693(90)90176-O`, originally owns Griess source grading/phase and Albert construction. Classical finite projective geometry PG(2,3), cubic W(B3) and rational Maschke/cyclotomic C13 representation results are NOT DASHI inventions. Agda #1249 owns original Cube27 antipode and adjacency; Agda #1261 owns punctured nine-sheet crystal provenance; Lean #52 owns the already constructed rational Albert/J0 source actor. Ibrahim A027907/OEIS work and the existing Sloane/McGarvey/Foster/Riordan contributor genealogy owns the original trinomial/path-cube arithmetic as appropriate. Chen–Lam–Shimakura (2018) own the separate Monster Z3 VOA source, not this 27D Albert. Alsaody–Gille (2019) and Barry–Tignol (2023) own triality/isotope sources separately. Source existence ≠ attributed fact ≠ external corroboration ≠ local computation ≠ source-written code ≠ kernel proof ≠ physical measurement.
