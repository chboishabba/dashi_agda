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

## 26 October 2026 post-refresh exact max-cut: one Griess C13 actor, zero spatial cube edges

Original mathematical root: **Robert L. Griess Jr.**, *A Moufang loop, the exceptional Jordan algebra, and a cubic form in 27 variables*, J. Algebra 131 (1990), 281–293, DOI 10.1016/0021-8693(90)90176-O. His original source F3³ grading / AL normalizer and Moufang loop are NOT new findings here. Prior cubic geometry and classical graph covering are original literature: **Jonathan L. Gross (1974)** voltage graphs DOI 10.1016/0012-365X(74)90006-5 and **Gross–Tucker (1977)** permutation voltage covers DOI 10.1016/0012-365X(77)90131-5. Preserve classic PG(2,3), Maschke/C13 representation authorship and original IBM / OEIS Sloane–McGarvey–Foster/Riordan provenance owners separately; no conflated novelty claims.

**What previous PRs already own:** Agda #1249 native nonwrapping P3³ cube, native antipode and its exact 26→13×Bool quotient with odd four-cycle holonomy; Agda #1261 punctured27 three-sheet 8+9+9 and 13-axis support 3+6+4; Lean #52 SOURCE Griess order13 (three corrected shears), actual rational Albert Jordan27/tracezero26 and exact 26×26 rational C13 linear intertwiner `B X = X P`, `det(X)=-729/4096 ≠0`. New work adds **only truly missing action/edge discriminator**, not another cube/Albert model.

The selected *SOURCE* grade action is `M(x0,x1,x2)=(x0+x1,x1+x2,x0+x1+x2) mod3`; its coordinate columns have support 2,3,2. An original P3³ native edge changes exactly one axis (0↔+1 or 0↔−1). Thus **ALL 54/54 full cube edges become NONEDGES** and **ALL 48/48 original punctured nonzero cube edges become NONEDGES** under the same actor, not merely the previously published one origin-adjacent edge. Exact independently executed Python `check_griess_13_punctured27_full_edge_obstruction.py` PASS with SHA256 `3c63bdad3afca5e1766230501f70403bb2141a6b71dac938b3de6b9c630632a2`; receipt JSON persisted. Source-written Lean #52 `Griess1990Projective13PuncturedCube27SameGrade.lean` now contains universal all-edge obstruction, 24 quotient-graph edge count, 9 degree4 + 4 degree3 count and its selected 13-cycle non-descent; the selected actor has only **5/24 quotient edges mapping to other quotient edges**.

**Existing nontrivial Z2 voltage-cover geometry:** projective 13-axis spatial graph (13 vertices,24 edges, b1=12) has original signed punctured 26-site **connected double cover** (26 vertices,48 edges,b1=23=2×12−1). Native quotient's explicit four-edge cycle has XOR voltage1, no global adjacency-preserving sign section. This is NOT the unrelated PG(2,3) dual 13×13 incidence relation with 52 flags. It is not physical holonomy.

**Positive protected:** The grade-order13 action has two actual 13-cycles on the 26 nonzero label SET. The free rational space of functions on these labels carries permutation P, genuinely intertwinable with the existing 26-dimensional tracezero rational Albert C13 action B via explicit invertible X. That **does not** intertwine original P3³ graph adjacency, Albert Jordan product or a physical 26-dimensional string target. Earlier independent local C13 rational certificate rerun PASS with correct JSON argument.

**Latest additional PR #1260:** `Z[ω]/(1−ω)^9` has the *same cardinal* `3^9=81×243=19683`, but its additive group is `C81×C243`, not `(C3)^9`, and not the nonassociative exponent-three Moufang `M81×(C3)^5` under loop multiplication. The finite cyclic group has elements of order243, whereas the latter trit structures have exponent3; its 3-torsion has 9 elements versus the elementary group's 19683. This is a decisive *NO-ID* arithmetic source discriminator. Do not graft onto #1260's separate Pickover/RH claims. Agda #1250's original Monster-selected 78 character/6.Suz task is similarly distinct: no selected same-actor/class intertwiner follows from repeated 13/26/78.

**Canonical detailed source-graded Pareto ledger:** [Lean #52 2026-10-26 source-grade/all-edge/no-go](https://github.com/chboishabba/dashi_lean4/blob/agent/albert-jordan-f4-maxcut-20261007/docs/superpowers/plans/2026-10-26-punctured27-projective13-all-edge-obstruction-and-source-snowball.md). Standalone portable finite regression added identically to Lean #52 and Agda #1249 as `scripts/check_griess13_source_action_native_cube_edge_no_go.py`; new Lean proof source and exact GitHub Python bytes were not kernel-tested or exact-byte replayed. No CI, Agda or Lean kernel success represented. Next Pareto: Lean/Agda typecheck actual original Jordan products, 26×26 invertible C13 representation, native sign quotient/odd voltage. Full exceptional F4, selected Monster 3B, physical observable/RH gates remain independent.

### 2026-10-26 final missing source-graph section payment (after latest concurrent #1249 refresh)
The pre-existing `noEdgeCompatibleOrientation` Boolean XOR impossibility was mathematically correct but, alone, conditional on four sign equations. **New Agda #1249 typed source** `DASHI/Unified/HyperfabricPunctured27Projective13OrientationExact.agda` now defines FOUR lemmas `spatialEdgeBit{XFacePP,FacePPAxisY,AxisYFacePM,FacePMAxisX}` deriving those same equations from the **ACTUAL native Cube.HypervoxelAdjacent** on each of the four explicitly selected quotient edges. It composes those four edge-to-bit lemmas with the old finite 16-case contradiction as **`noSpatialSectionOnNativeFourCycle`**, thus presenting a direct theorem on the original native graph, not a naked XOR premise. Unlike prior source-only ledger claims, the *graph-to-XOR link itself* is now included as an Agda theorem target; **still no Agda typecheck/kernel receipt**.

Independent exact local source-equivalent check `/mnt/data/check_cube27_native_four_edge_sign_section.py` **PASS** all 16 actual signed edge incidences and exhaustively rejects all 16 four-vertex orientation choices; receipt `/mnt/data/cube27_native_four_edge_sign_section_receipt.json`. Portable finite regression `scripts/check_griess13_source_action_native_cube_edge_no_go.py` on both Lean #52 and Agda #1249 carries the same four-edge audit; concurrent Agda #1249 branch changes were inspected and existing modified files reconciled before the accepted write, not overwritten. This is classical graph-covering `Z2` voltage theory (Gross 1974; Gross–Tucker 1977), *not* experimental electromagnetic gauge holonomy or proof of a quantum computer.


## 2026-10-27 completion: exact full-source COMMUTANT, 1+12+13 projectors

The original source-grade permutation module (FREE Q linearisation of **26 nonzero F3³ point labels**) has **precisely three** ordered-pair orbitals under six actual elementary SL3(3) shears: diagonal 26, antipodal 26, linearly-independent 624. Therefore its **entire** Q-linear endomorphism commutant is the 3D adjacency algebra `span_Q{I,T,J}`, where `T` is the actual antipodal permutation and `J` all-ones. Original structural result is classical finite permutation/invariant theory; this **particular F3³/source-graph instantiation** is new repository finite computation attributed to DASHI authorship with ChatGPT assistance; it is not in itself a full Albert J0/F4 action theorem.

The rational central primitive idempotents have actual ranks `1+12+13`:
```
P1 = J/26,
P12 = (I+T)/2 - J/26,
P13 = (I-T)/2.
```
Exact Python checked `P_i²=P_i`, `P_iP_j=0` for i≠j and `Σ P_i=I` both by literal 26×26 Fraction matrices and by elementary `I,T,J` multiplication `T²=I, JT=TJ=J, J²=26J`. Hence *every* invariant operator is scalar on the anti-antipodal 13D sector, not merely the particular Reynolds average. This is the sharper universal blocker for carrying the ORIGINAL signed spatial quotient adjacency into a full source-group symmetric operator. The source selected **C13** subgroup has weaker symmetry; under C13, the same 26 grades decompose `(1+12)+(1+12)`, distinct from full group `1+12+13`. Actual native Albert J0 26D has a proved **local Python-only C13** intertwiner `BX=XP`, which **does not** imply the full SL3 equivalence.

Lean #52 added `sourceTrivialProjector`, `sourceEvenNonconstantProjector`, `sourceOddProjector` and corresponding sum/idempotence/orthogonality/trace proof targets in `Integration/Griess1990Punctured27SourceReynolds.lean`. The universal signed 13-sector scalar identity is stated for arbitrary orbital weights. Same existing independent `scripts/check_griess_punctured27_source_reynolds.py` was **extended in place** on Lean #52 and Agda #1249 with exact 3D algebra checks; new GitHub blob not byte-replayed here. Independently LOCAL standard-library `/mnt/data/check_griess_sl3_reynolds_adjacency.py` (SHA256 in updated `griess_sl3_reynolds_adjacency_receipt.json`) checked the full 26×26 rational idempotents and the ordered-pair BFS; PASS. Source-written Lean **KERNEL PENDING**, Agda-native source carrier proof unchanged. No physical gauge flux, full F4/Jordan action or selected Monster VOA follows.

**Pareto front:** close C13 and full SL3 source-grade OPERATOR projections computationally; pay Lean/Lake source grammar/typecheck, original 729 Jordan products, and the finite projector/commutant theorem chain next. Do NOT keep optimizing finite numeric matches (13/26/27/81/240/243/888), nor promote source-graded permutations to crystal adjacency or real Hamiltonians. Attribution stays Griess Jr. (1990) for the graded exceptional algebra, Gross / Gross--Tucker for classical graph covers, classical Reynolds/Maschke for averaging/decomposition, and existing Ibrahim/OEIS contributor lineage for the trinomial path-cube arithmetic.
