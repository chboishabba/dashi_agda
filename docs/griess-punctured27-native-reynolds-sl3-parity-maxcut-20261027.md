# Max-cut 2026-10-27 — Griess source action vs native punctured-27 graph: exact Reynolds projection

## User prompt / non-negotiable provenance

Original investigation: why a selected raw octonionic triality residual `883/8` lies near `888/8`; what would **force** a value of 888. The original rational source-to-native Albert related triple had zero **invariant** 729-product mismatch, unlike the noncanonical 60-degree SO rotation that reaches raw 888/8 with changed raw target norm. Preserve the selected source, avoid re-fitting a coincidental integer. Subsequent legitimate progress: original Griess 1990 finite Moufang81 associator `δg=det_F3^3`, source-corrected order13 Jordan automorphism, original signed 27 P3³ puncture (26→13×2), exact rational C13 module intertwiner with traceless Albert26, and *negative* native graph/Jordan operator intertwiners.

## Current original mathematical and repository source owners

1. **R. L. Griess Jr.**, *A Moufang loop, the exceptional Jordan algebra, and a cubic form in 27 variables*, **Journal of Algebra** 131 (1990), 281–293, DOI [10.1016/0021-8693(90)90176-O](https://doi.org/10.1016/0021-8693(90)90176-O): original graded exceptional Jordan algebra, source normalizer `F3³:SL3(3)`, Moufang quotient order81, not a DASHI discovery. Math: source **grade label action**; the spatial graph is separately chosen.
2. **Classical Reynolds / group averaging**: averaging a finite orthogonal group action yields the orthogonal projection onto invariant operators. General mathematical prior art (see [Reynolds operator](https://mathworld.wolfram.com/ReynoldsOperator.html) and standard invariant theory); the finite numerical instantiation below is new repository work, not a newly proved averaging theorem.
3. **Jonathan L. Gross (1974)**, *Voltage graphs*, Discrete Mathematics 9, 239–246, DOI [10.1016/0012-365X(74)90006-5](https://doi.org/10.1016/0012-365X(74)90006-5); **Jonathan L. Gross and Thomas W. Tucker (1977)**, *Generating all graph coverings by permutation voltage assignments*, Discrete Mathematics 18, 273–283, DOI [10.1016/0012-365X(77)90131-5](https://doi.org/10.1016/0012-365X(77)90131-5): independent sources for signed two-fold graph cover/voltage vocabulary, not experimental gauge flux.
4. **Agda #1249** `Hyperfabric27MinusOneAntipodalSameCarrierCutExact` ORIGINAL native `P3³` graph/antipode and `HyperfabricPunctured27Projective13OrientationExact` actual odd XOR cycle/no-section. **Agda #1261** `Punctured27NineSheetBridgeExact`, 26=8+9+9, 13 cubic axes 3+6+4. **Lean #52** original Griess `Grade`/true source-corrected shears, explicit 26 rational Albert (C13) module `BX=XP` / det X≠0, and source ORIGINAL projective-13 graph spectra.
5. **Ibrahim/OEIS A027907 contributor history** and existing proof/attribution owners supply path-cube trinomial counts, `26=2×13` and support-size arithmetic as appropriate; do not retroactively attribute Reynolds averaging or the original Griess action to those numerical observations.
6. **Chen–Lam–Shimakura**'s true Monster `Vsharp≅Vnatural` three-sector VOA remains a distinct original mathematical source. Do not transfer C13 / graph / finite Albert results to the selected Monster 3B VOA, F4 full rational group, bosonic strings or physical crystal systems without a SAME SOURCE OPERATOR proof.

## 1. ACTUAL selected order13 source-action Reynolds orthogonal projection

Let `V=F3³\{0}` be the original 26 centered ternary grades; `A∈Z^{26×26}` is the **real** nonwrapping original punctured `P3³` adjacency with **48 unordered/96 directed edges**. Let `P` be the ACTUAL grade permutation induced by the three previously source-corrected order13 shears `e01→e12→e20`. Exact source action `P^{13}=I` with two 13-cycles. Define `Z=Σ_(k=0..12) P^{-k} A P^k` and `A_C=Z/13`.

**Exact independent local standard-library Python PASS**:
- All `C(26,2)=325` unordered pairs form 25 order13 orbits, each 13 pairs, with number of ORIGINAL spatial edges `m` per pair-orbit distributed **3 orbits with m=0, 6 with m=1, 6 with m=2, 10 with m=3**; weighted projected edge value is `m/13`, NOT an original 0/1 graph edge. Sum original edges `6*1+6*2+10*3=48`.
- `Pᵀ Z P=Z`, `Z=Zᵀ`; the exact orthogonal inner-product identity `13⟨A,Z⟩=⟨Z,Z⟩` confirms the residual is perpendicular to the invariant projection.
- `||A||_F²=96`; `||Z||_F²=3120`; `⟨A,Z⟩=240`; `||13A-Z||_F²=13104`.
- Therefore `||A_C||_F²=240/13`, `||A-A_C||_F²=1008/13`: **retained 5/26** and **lost 21/26** of original squared norm.
- Original antipodal 13 even / 13 signed-odd spatial parity sectors commute with P. The averaged EVEN block retains **14/39** of original even-sector norm²; the ODD signed block retains **1/39**. This is source-specific, NOT a claim that the signed holonomy has physically dissipated.

By standard finite-group unitary averaging, `A_C` is the **unique closest C13-equivariant real matrix** to A under Frobenius distance. No same-native-Albert Jordan multiplication is claimed.

## 2. FULL original SL3(3) label action: stronger, exact complete pair-orbit cut

Reuse all SIX earlier `Griess1990Moufang81ElementaryLift.gradeShear` elementary shears; no invented group. The source grade group acts on all `26²=676` ordered nonzero-grade pairs. Independent exact BFS under six generators produces EXACTLY THREE orbits:
- equal pairs `x=y`: size 26, zero original graph edges;
- antipodal pairs `x=-y`: size 26, zero original graph edges;
- linearly independent pairs: size 624, ALL **96** original directed edges.

Consequently the FULL Reynolds projection is the explicit, unique source-invariant weighted matrix
```
A_SL3 = (2/13) * (J26 - I26 - T_antipode).
```
Its plus/minus antipodal parity block is
```
A_SL3,+ = (4/13)*(J13 - I13);
A_SL3,- = 0.
```
Exact spectra: 48/13 with multiplicity1; -4/13 with multiplicity12; zero with multiplicity13. Exact `||A_SL3||²=192/13` and `||A-A_SL3||²=1056/13`; norm² fraction retained **2/13**, fraction lost **11/13**. The source group's full symmetry *annihilates the entire original signed 13-dimensional spatial adjacency sector* under best invariant approximation. This does NOT assert that the abstract 13D signed site space disappears, that the original C13 module weld fails, or that an SL3 representation of native Albert J0 is already constructed.

## 3. Implementations and checks

- **Lean #52** `Integration/Griess1990Punctured27SourceReynolds.lean` directly imports existing original Griess `Grade`, original spatial path adjacency and order13 source cycles; states finite exact source-specific `Z` symmetry, integer norms/cross norm, small average formula and six-shear/full-source odd-sector zero obligations. **Source-written, NOT kernel checked.**
- **Lean #52 + Agda #1249** identical `scripts/check_griess_punctured27_source_reynolds.py` standard-library-only exact regression checks **both** actions and finite orbit decompositions. Exact committed script blobs were not independently replayed in the authoring runtime.
- **Actual executed LOCAL independent full scripts**: `/mnt/data/check_griess_c13_reynolds_nearest_adjacency.py`, receipt `/mnt/data/griess_c13_reynolds_nearest_adjacency_receipt.json`; `/mnt/data/check_griess_sl3_reynolds_adjacency.py`, receipt `/mnt/data/griess_sl3_reynolds_adjacency_receipt.json`. These DID execute PASS with exact integers/Fractions and SHA-256 receipts; not Lean/Agda kernel.
- Existing native spectral `13+13` (signed) Gram/characteristic polynomial checks and actual rational `BX=XP` Albert J0 remain unchanged and independently checked. The **original** spatial graph P3³ is NOT invariant under selected SL3, and the full source action should not be promoted into an exceptional Jordan-product or Monster same-object theorem by analogy.

## 4. Pareto / Ibrahim stop rules

**Computationally CLOSED** for the specified source graph and source grade actions: both projections, closest-invariant property by classical Reynolds theorem, exact retained energy, full-source loss of signed adjacency, and original graph/Jordan-separation counterexamples.

**Formal P0 OPEN**: actual Lean/Lake kernel verification of Griess 1990 source-to-native 729 Jordan product, exact source shear action and `BX=XP`; new Lean integer Reynolds Z/N and full six-shear/orbit receipts. The Mathlib kernel hasn't run in this runtime. Agda native XOR/antipode proofs source-written but still untypechecked.

**P1 DISTINCT**: full `SL3(3)` action on ACTUAL native Albert traceless26 and any same-full-group intertwiner is **not** established by the C13-only rational X; source-selected Monster VOA 3B remains elsewhere, and physical NV/KK/string/RH require separately sourced observables. Do not confuse label symmetry and actual Hamiltonian symmetry.

**Proof/status invariant**: original author/date → original statement → independent exact local computation → committed code → kernel certificate → external observation are separate edges; only paid edges may be composed. Original mathematics credited to Griess, Reynolds/classical invariant theory and Gross/Gross–Tucker; finite derived checks credited to the repo contributors, with current ChatGPT assistance; Ibrahim/OEIS contributor attribution retained in preexisting owners.


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


## 2026-10-27 higher Pareto discriminator: SELECTED shear character NO-FULL-26 weld

**New source-specific actual algebra receipt:** six ALREADY OWNER-DEFINED Griess corrected elementary grade shears `e01,e02,e10,e12,e20,e21` (in Lean #52 `Griess1990Moufang81ElementaryLift`, Agda #1239 companions) were compared, including true original homogeneous `e_x ↦ ω^{h_s(x)} e_{M_sx}` phase, rather than grade-permutation only. Each source 27D actor fixes NINE grades but the original phase correction changes its rational tau-real character:

| Exact selected lift | Fixed-grade phase histogram (1,ω,ω²) | Original Albert27 trace | Actual traceless Albert J0(26) trace | 26 nonzero-GRADE permutation trace |
| --- | --- | --- | --- | --- |
| e01,e10,e12,e21 | (3,3,3) | 0 | **−1** | **8** |
| e02,e20 | (9,0,0) | 9 | 8 | 8 |

The fixed original Albert unit contributes trace1, so J0 trace = source27 trace−1. The original 26 grade-label permutation fixes eight nonzero grades under ALL six elementary shears. The source formula's cyclotomic eigenvalue sum is exact in Q(ω), no numerical near-match. Since rational similar matrices have equal traces, there can be NO **e01**-equivariant extension of the existing `BX=XP` rational C13 intertwiner that carries the ORIGINAL grade26 permutation into this SELECTED true Griess/J0 lift. A positive C13-only isomorphism does not imply a six-generator extension.

**Independent stronger actual-product receipt:** local `/mnt/data/check_griess_shear_e01_actual_Jordan_character.py` reconstructs the ORIGINAL Q(ω) tau-real basis and source product (via pre-existing `check_griess1990_standalone_crossprover.py`), checks all **729** Jordan basis products for **each** of e01 and e02, order3, unit and trace27=0/9. PASS. Local `check_griess_shears_character_no_full26.py` enumerates the six phase histograms and trace discrepancy, PASS, with `griess_source_six_shears_character_no_full26_receipt.json`. A different central-character correction may give an inequivalent LIFT of the same grade shear and change the character; these are *selected-lift* obstructions, not the proof that every coherent lift/SL3 section fails. An actual full-group section is a DIFFERENT unpaid representation and group-relations problem.

**Committed Lean #52:** `Integration/Griess1990SourceShearCharacterNoFull26.lean` reuses actual original `g` formula/Cyclo and the real selected `phaseCorrection`/Shear owners. It states six finite phase/traces and selected e01 non-equality. Any initial generic trace-cyclicity proof hole was removed immediately; **no sorry/admit remains**. These are source-written proof targets, Lean kernel UNCHECKED. Cross-repository identical optional literal-source test script `scripts/check_griess_source_six_shears_character_no_full26.py` committed to Lean #52 and Agda #1239, using the preexisting original source table donor and failing if missing. Exact GitHub bytes were not byte-for-byte executed. Locally source-equivalent scripts above **DID run** and passed.

**New snowball-original mathematical roots; do not erase provenance:**
- **Robert L. Griess Jr.**, *The splitting of extensions of SL(3,3) by the vector space F₃³*, **Pacific Journal of Mathematics 63** (1976), 405–409, DOI [10.2140/pjm.1976.63.405](https://doi.org/10.2140/pjm.1976.63.405). This is directly relevant to the unpaid precise selection of a coherent SL3 complement/section inside the source extended automorphism group. Its actual theorem statement must be read before any splitting claim is promoted.
- **Lucien Bénéteau and J. Lacaze** (1980), *Groupes d'Automorphismes des Boucles de Moufang Commutatives*, European Journal of Combinatorics 1, 299–309, DOI [10.1016/S0195-6698(80)80029-1](https://doi.org/10.1016/S0195-6698(80)80029-1), independent commutative-Moufang automorphism theory. No original-source result is reattributed to DASHI.
- **Griess Jr. 1990** (J Algebra 131:281–293 DOI 10.1016/0021-8693(90)90176-O) remains original authority for this PARTICULAR 81-loop, g and graded exceptional 27 Jordan construction.
- Gross 1974/Gross–Tucker 1977 remain independent classic ORIGINAL graph-cover sources; Reynolds theory is independent classical group averaging; Agda #1249 original P3³, #1261 original crystal 13-axis, Ibrahim/OEIS original A027907 numeric source, Chen–Lam–Shimakura real 3-sector Moonshine VOA remain separate owned streams.

**Pareto change**: FULL S L3 *grade-label* commutant `1+12+13` and spatial Reynolds projection computationally CLOSED; a purported identification of the native Albert traceless J0 with the grade26 permutation for THESE six lifted source generators is now NEGATIVELY CLOSED by the selected e01 trace. Next meaningful positive producer: recover and kernel-certify a **coherent source SL3 complement**, if it exists for the selected rational form, using Griess 1976 and original 1990/previous loop owner; check each generator source multiplication and their finite group relations/characters, then independently test module intertwiners. No assertion that this alternative section must exist over the selected rational form. More urgent still: Lean/Lake kernel receipts for original 729 source/native products and existing new finite proofs; Agda original sign/holonomy compilation. Stop doing ungrounded 13/26/27/81/888 value coincidences.


## 2026-10-27 original Sah/Griess SPLITTING theorem read; exact dual-kernel paid

The previous note deferred checking the original 1976 theorem. **That deferral is now resolved**: we opened and visually inspected the source PDF (pages 405 and 409). **R. L. Griess Jr., Pacific Journal of Mathematics 63 (1976), 405–409**, DOI [10.2140/pjm.1976.63.405](https://doi.org/10.2140/pjm.1976.63.405), proves the actual `H²(SL(3,3),F3³_natural)=0` and splitting of extensions with the specified natural action. The paper's INTRO explicitly says the result had already appeared in work by **Chih-Han Sah**. Cite and preserve **C.-H. Sah**, *Cohomology of split group extensions*, J. Algebra 29 (1974), 255–302, as the earlier cohomological source; attribute Griess's *two 1976 proofs* separately. Neither source claims our local particular choice of six corrected lifts is a homomorphic section.

**NEW SAME-SOURCE kernel conjugation test**: On Griess 1990's actual 81-element Moufang loop, all `6×27×81=13122` exact combinations pass:
```
L_s · T_lambda · L_s^{-1} = T_(lambda ∘ M_s^{-1}),
M_s∈SL3(3), T_lambda(x,a)=(x,a+lambda·x).
```
Here `lambda` belongs to the 27-element **DUAL/CONTRAGREDIENT** of the natural F3³ grade module; elementary shear e_ij acts by `lambda_j <- lambda_j-lambda_i`. The pairing `(M_s^-T lambda)·(M_s x)=lambda·x` is exhaustively checked. The dual representation is obtained by precomposing the natural module with the graph automorphism `M→M^-T`, so cohomology vanishing transfers by this reindexing. Given the already independently computed source finite group order151632, quotient SL3 order5616 and kernel27, the **ABSTRACT splitting obstruction is already zero by published original mathematics** (subject to formal exact-sequence/kernel identification). The remaining gap is a SELECTED, ACTUALLY CONSTRUCTED section and its group relations/character, not more ad hoc numerical matching.

**NEW selected-lift negative acceptance test:** grade e01 and e20 are conjugate by the orientation-preserving three-coordinate permutation `(x0,x1,x2)↦(x1,x2,x0)`. Exact local Python on all 27 grades PASSED. But their CURRENTly CHOSEN original homogeneous Griess actual Albert J0 traces are **−1** and **8** respectively, both fully source-corrected Jordan automorphisms. Therefore the present six chosen automorphisms CANNOT be the generators of one coherent homomorphic SL3 section respecting those grade elements; conjugate elements in a representation must have equal trace. This does NOT contradict Sah/Griess splitting and does NOT preclude a different, kernel-character-adjusted set of lifts.

Lean #52 `Integration/Griess1990MoufangDualKernelSplitGate.lean` uses original ACTUAL `centralCharacterShift` and `lift` owners for 13122 finite source dual conjugacy/pairing targets, no imported/assumed `H²` axiom. `Integration/Griess1990SourceShearCharacterNoFull26.lean` adds the actual cyclic grade conjugator and selected character non-equality, no `sorry` or `admit`. Matching Python source regressions `scripts/check_griess_M81_sah1974_griess1976_dual_kernel.py` and `check_griess_source_six_shears_character_no_full26.py` committed Lean #52/Agda #1239. Local independently executed scripts `/mnt/data/check_griess_source_dual_kernel_split1976_gate.py`, `/mnt/data/check_griess_shears_character_no_full26.py`, and actual literal 729×2 Jordan test `/mnt/data/check_griess_shear_e01_actual_Jordan_character.py` all PASS. New committed scripts were not byte-identically replayed and Lean/Agda kernels unavailable; **NO invented kernel success**.

**Pareto revised:** original abstract splitting is PUBLISHED/CLOSED, concrete full-source 27-to-26 **same coherent SL3 action** and canonical group-section constructor are OPEN. Construct with actual 1974 Sah/1976 Griess module and a certified section (or source's existing explicit complement), prove kernel exact sequence, then recalculate selected characters and potential new full-action intertwiners. The old arbitrary lifted-six-shear J0↔grade26 identification is NEGATIVELY CLOSED. Native P3³ adjacency/signed holonomy remains forbidden by the original spatial operator no-go, and the existing positive selected C13 rational Albert26 is unaffected. Respect original authorship and all role/donor statuses.


## 2026-10-27 BIDI breakthrough: coherent FULL SL3 section finally explicit, Albert J0 IRREDUCIBLE, C13 retained

**P0 positive source producer mathematically now CLOSED by exact finite computation:** the earlier selected six Griess M81 shear lifts generated all 151632 automorphisms, NOT a splitting section, even after independently normalizing their traces. We solved the correct global system: 18 F3 character coordinates, all **5616** original-grade SL3(3) elements, **33696** generator transitions, **758187** exact F3 equations. Rank **15** with three free parameters and **27** EXACT coherent solutions; all are conjugate by the original **27** central characters. Explicit correction `λ_s` (left output) for e01/e02/e10/e12/e20/e21:
```
(0,0,0) (0,2,0) (0,0,1) (2,0,0) (0,1,0) (0,0,0)
```
Independent SymPy on the LITERAL 81 source-loop elements confirms the six corrected lifts generate exactly **5616** automorphisms and project onto ALL **5616** original SL3 grade maps, so the 27-kernel intersection is trivial: **CONSTRUCTIVE COMPLEMENT**. Existing source Griess tau-real 27D Jordan basis rebuilt independently and **4374/4374** original products (six×729) PASS. Every coherent elementary shear has fixed-grade phase classes (3,3,3), trace27=0, and true J0 trace −1; original 26-grade permutation trace8. The *published abstract* vanishing `H²(SL3(3),F3³)=0` is original **Sah (1974) / Griess (1976)**, NOT a new DASHI theorem. Griess 1976 explicitly credits Sah and V. Landazuri for an alternative proof. Source 1976 references the Sah credit as `[6]`, but the end reference numbered [6] is Mac Lane; Griess 1990 correctly lists Sah as independent bibliography. Preserve that discrepancy, do not manufacture priority.

**P0 strongest negative / full-group representation**: exact independent 5616-element SOURCE character enumerations agree (symbolic GF3 action and actual 81-permutation group) for true **native-compatible traceless Albert J0 dimension26**:
```
char χ_J0   26:1, 2:819, 0:3132, -1:1664.
Σ χ²=5616, |SL3|=5616, 〈χ,χ〉=1 (absolutely irreducible).
```
The original 26 nonzero F3³ **point-label permutation** module instead has `〈χ,χ〉=3` and a full-source-grade commutant span `{I,T,J}` with 1+12+13 rational projectors, as PAID earlier in this PR. Hence **NO full SL3 equivariant grade26↔AlbertJ0 rational linear identification** under ANY of the 27 conjugate actual section choices, although the selected C13-restricted modules are isomorphic. Distinct group representation scope, not a physical/Monster/VOA no-go.

**P0 positive two-sided C13 RECOVERY on actual coherent complement**: new e01→e12→e20 word is not literally previous arbitrary e01/e12/e20 word, but `new=T_(2,1,0) old=T_(1,1,2) old T_-(1,1,2)` on all 81 SOURCE M81 states. Local native Q-Albert 27/26 certificates PASS: the Kν-conjugator on actual native J0 has determinant1, its inherited 26×26 C13 intertwiner `Y=Kν X` obeys `B_new Y=Y P_two13`, **det Y=-729/4096≠0** (same as old selected X). This explicitly preserves the strongest affirmative cyclic bridge while rigorously rejecting its attempted FULL SL3 extension.

**New code/formal owners**:
- Lean #52 `Integration/Griess1990MoufangCoherentSL3Section.lean`: reuses actual Loop81/phase/shears/central characters, defines six corrections, the actual source multiplication/order/unit, sample Steinberg group relations, all-six trace histogram, exact order13 word conjugacy; SOURCE-WRITTEN, Lean kernel NOT RUN. No `sorry` or `admit` tactic proof hole.
- Agda #1239 `DASHI/Moonshine/Griess1990MoufangCoherentSL3SectionSourceExact.agda`: reuses original Griess carrier and phase; defines actual six coherent source lifts and 81 native `refl` examples for e01/e02 commutation and 81 for coherent-vs-old order13 source shift; Agda kernel NOT RUN.
- BOTH repo PRs `scripts/check_griess_M81_coherent_SL3_section_steelman_bidi.py` (standalone independent 18-variable rank15 GF3 exact solver, 5616 permutation order/character), `scripts/check_griess_coherent_section_original_jordan_4374.py` (calls pre-existing source product checker and tests all six×729 actual original products), and `scripts/check_griess_coherent_C13_albert26_conjugacy_bidi.py` (source all81 by default and optional ORIGINAL native rational input certificates). GitHub exact newly committed script bytes NOT independently replayed in local runtime, but separately LOCAL full solver and original source/product/native conjugacy programs DID execute PASS, with SHA256 and JSON receipts.
- [Full original-source STEELMAN/BIDI ledger on Lean #52](https://github.com/chboishabba/dashi_lean4/blob/agent/albert-jordan-f4-maxcut-20261007/docs/superpowers/plans/2026-10-27-griess-sah-coherent-sl3-albert26-irreducible-bidi-maxcut.md), [Agda #1239 source-owner companion](https://github.com/chboishabba/dashi_agda/blob/chatgpt/c3-nine-site-borromean-braid-20261022/docs/griess-sah-coherent-sl3-albert26-bidi-maxcut-20261027.md).

**Pareto phase correction**: previous roadmaps saying “concrete coherent SL3 splitting section remains open” are SUPERSEDED by the exact finite source construction; what remains open is KERNEL typechecking and a fully **Lean-verified abstract group action/homomorphism** over all 5616 elements, plus Agda same-object transport. This does NOT make earlier native P3³ signed adjacency, 240/E8 fixed Weyl-root action, experimental diamond NV, Monster 3B selected VOA or physical KK/string/RH corresponding actors valid; they remain independently typed and the original 883/888 raw coordinate-norm question is already bounded.


## 2026-10-27 next PARETO/STEELMAN proof cut: full ZERO-Hom, cyclic FIFTY-TWO-Hom

This is NEW evidence beyond the previous `χ²_J0=1` vs `χ²_grade=3` no-full-isomorphism argument. An exact rerun of the already original-source, original-M81 coherent **5616-element** finite complement shows the SAME literal group has the following **JOINT** character bins:
```
(χ_J0, χ_grade26, multiplicity):
(26,26,1); (2,2,819); (0,0,3132); (-1,2,1560); (-1,8,104).
```
Consequently the MIXED inner-product numerator is
```
26*26 + 819*2*2 + 3132*0*0 -1560*2 -104*8
 = 676+3276-3120-832 = 0.
```
Classical finite-group character orthogonality then gives the **strictly stronger exact obstruction**
`dim_C Hom_SL3(J0_C, C[F3³\{0}])=0` and reverse Hom=0, not merely `J0≄grade26`. Complex zero implies rational Hom zero. This holds for all **27 conjugate source coherent complements**, as central-character conjugation does not change characters; check is about the SAME original selected actual Griess action, not any arbitrary 26D module. The **selected coherent order13** word is correctly composed as e01 then e12 then e20; Python SymPy permutation products use the **left-to-right** convention for this implementation. A first audit using reversed order produced order8 and was REJECTED, not promoted. Correct word has order13 and BOTH 26D characters are 26 at identity, 0 on all 12 nonidentity powers, so
`dim_C Hom_C13(J0_C, grade26_C)=(26²)/13=52`.
Thus **0 full SL3 intertwiners vs 52 cyclic intertwiners**, even though an earlier explicit invertible **Q[C13]** matrix X exists. This is stronger BIDI closure: full action ANY NONZERO map impossible, cyclic many maps.

**Exact independent LOCAL rerun**: `/mnt/data/check_griess_full_SL3_vs_C13_intertwiner_space.py` reruns the prior exact generator/linear-system solver and enumerates the ACTUAL 5616 **81-point** permutations independently; PASS, with `/mnt/data/griess_full_SL3_vs_C13_Hom_zero_receipt.json` and SHA256. It consumed the previously verified local source solver and original M81 permutation action, not synthetic characters. **Committed reproducible scripts** on Lean #52 and Agda #1239: `scripts/check_griess_coherent_SL3_C13_zeroHom_joint_character.py`, whose source code was generated separately and has NOT been byte-identically replayed locally. The selected order13 product order regression is mandatory.

**Formal source:** Lean #52 `Integration/Griess1990CoherentSL3VsC13ZeroHomCharacter.lean` adds fully explicit five-bin signed integer/norm certificate proof targets and conditional `FDRep.scalar_product_char_eq_finrank_equivariant` using **the EXISTING Mathlib representation-theory owner** (do not re-prove character orthogonality). Agda #1239 `DASHI/Moonshine/Griess1990CoherentSL3VsC13ZeroHomArithmeticExact.agda` adds exact natural-number cancellation of the positive and negative terms and 13×52 identity. Lean/Agda theorem sources remain **SOURCE-WRITTEN; neither kernel invoked**. The conditional Lean theorem takes the actual representation/character-sum payment as an explicit hypothesis; DO NOT claim the histogram-to-source group theorem has been kernel-proved.

**Source roles:** Griess 1990 *original* 81 Moufang/Albert product and its original normalizer, Sah (1974)/Griess (1976) *original* abstract splitting, Maschke/Schur classical orthogonality, Antoine Labelle and Mathlib contributors *formal* original character API, DASHI PRs subsequent computations/source models, Ibrahim/OEIS 13/26 numeric lineage distinct, original native spatial graph Agda #1249 and crystal #1261 separate, Chen–Lam–Shimakura selected VOA sector still unpaid. Nothing here identifies P3³ nearest neighbour adjacency with Jordan multiplication or selected Monster 3B modes; no physical/experimental inference.
