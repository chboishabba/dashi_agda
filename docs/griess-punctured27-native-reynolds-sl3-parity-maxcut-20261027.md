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
