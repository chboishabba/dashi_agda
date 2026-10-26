# 2026-10-27 max-cut: coherent original Griess SL3 complement, irreducible Albert26, bidirectional claim adjudication

## Original question, what this does and does not answer

The original prompt was a surprise that 512 raw octonionic triality coefficients gave a chosen residual 883/8, close to 888/8, and asked **what source-defined algebra would force the difference**. It did NOT request proof of Monster, physics or RH. Earlier independently verified rational related-triple comparison gives a ZERO invariant Jordan product residual and 729 basis products; the one-plane 60-degree adjustment to 888/8 is noncanonical and changes raw norm. Subsequent genuine mathematical source: Griess 1990 27D Albert with F3³ grading and 81-element commutative Moufang quotient. The user then requested cross-pollination with 13/26 punctured 27, original 243→240, Ibrahim, and NOW explicit charitable STEELMAN/BIDIRECTIONAL verification.

## Original authorship and evidence genealogy, never collapse

1. **Chih-Han Sah**, *Cohomology of split group extensions*, **J. Algebra 29** (1974), 255–302. Original earlier cohomological result acknowledged by Griess. The Griess 1976 PDF's introduction references “Sah [6]” but its end bibliography entry numbered [6] is **Saunders Mac Lane, Homology**; avoid laundering that internal citation-number mismatch into a verified bibliography entry. Griess 1990's references include Sah by name correctly. Sah's wider cohomological research and this specific splitting statement must retain precise proposition attribution.
2. **Robert L. Griess Jr.**, *The splitting of extensions of SL(3,3) by the vector space F3³*, **Pacific J. Math. 63** (1976), 405–409, DOI [10.2140/pjm.1976.63.405](https://doi.org/10.2140/pjm.1976.63.405). Its source theorem explicitly states **H²(SL3(3),F3³)=0**; source also credits **V. Landazuri** for suggesting an alternate proof. Original abstract splitting is therefore PRIOR PUBLISHED mathematics.
3. **Robert L. Griess Jr.**, *A Moufang loop, the exceptional Jordan algebra, and a cubic form in 27 variables*, **J. Algebra 131** (1990), 281–293, DOI [10.1016/0021-8693(90)90176-O](https://doi.org/10.1016/0021-8693(90)90176-O). Original graded exceptional Albert product, original g(x,y), particular nonassociative M81 quotient, F3³:SL3(3) normalizer. The local explicit rational transport and finite solver are subsequent DASHI implementation, NOT original discoveries of those structures.
4. **Lucien Bénéteau, J. Lacaze**, *Groupes d'Automorphismes des Boucles de Moufang Commutatives*, **Eur. J. Combin. 1** (1980), 299–309, DOI [10.1016/S0195-6698(80)80029-1](https://doi.org/10.1016/S0195-6698(80)80029-1): independent automorphism-group results. Classical Maschke/Schur character orthogonality, Reynolds, and SL3(3) representation theory remain their original authorities.
5. Native original spatial P3³ antipode/graph is Agda #1249, Agda #1261 owns crystallographic 13-axis and 26=9+8+9, original OEIS/Ibrahim A027907 and Sloane/McGarvey/Foster/Riordan source roles stay in their attributed owners. Distinct C3 orbifold Monster VOA source by Chen–Lam–Shimakura is NOT a canonical 27D Albert↔VOA intertwiner. Gross/Gross–Tucker graph voltage covering and rational octonion triality donors remain independent.

## Charitable positive steelman: actually build the full algebra group section

ALREADY in Lean #52 and Agda #1239, original Griess source M81 is the literal 81-element loop with
`(x,a)*(y,b)=(x+y,a+b+g(x,y))`, original `g=-x0*x1*y2-x2*y0*y1+x1*x2*y0+x0*y1*y2 mod3`.
Six original source-corrected elementary transvections `e_ij` are actual loop automorphisms. They generate an extension of order151632 with 27 central character shifts and grade quotient SL3(3) of order5616; source kernel action is the exact DUAL F3³ module.

**P0 exact constructive result**: allow one additional left central-character shift `λ_s ·(M_s x)` per generator; six × three unknowns =18 variables over F3. For ALL 5616 quotient grade maps enumerate 33696 generator edges and 758187 affine linear compatibility equations. GF3 elimination yields:
- **rank 15**, consistency, 3 free parameters, **27 solutions**;
- chosen solution, generator order e01,e02,e10,e12,e20,e21:
```
e01: (0,0,0)
e02: (0,2,0)
e10: (0,0,1)
e12: (2,0,0)
e20: (0,1,0)
e21: (0,0,0).
```
- all 27 solutions are precisely distinct conjugates of this section by one of the original source's 27 central characters `T_mu`. For transvection `i<-i+j` conjugation shifts the output correction component `j` by `mu_i`. Rank 15 confirms NO additional independent chosen-generator sections.
- Actual separate SymPy permutation generation of those SIX literal 81-point Moufang-loop maps has order **5616**, with faithful grade image also of order5616: kernel intersection trivial, hence a **concrete section**, not a reported status Bool. Its sampled Chevalley/Steinberg relations e01/e02 commute and [e01,e12]=e02 also pass literal 81-point checks.
- Independent ORIGINAL Q(ω) homogeneous tau-real source Jordan algebra check: **729/729 products for EACH of six lifts**, **4374/4374 actual basis-product tests**, order3, unit, and trace27=0 for every coherent elementary transvection; traceless trace = -1. The uncorrected/individually normalised six shears generate 151632, so character-normalisation alone is insufficient.

**Local exact executed**: `/mnt/data/check_griess_coherent_sl3_section_steelman_bidi.py` performs FULL GF3 758187-equation solver, all 33696 edge replays, 27 section comparison and INDEPENDENT 5616-element permutation character check, with `griess_coherent_sl3_section_steelman_bidi_receipt.json` containing SHA-256 and provenance; separately `/mnt/data/check_griess_coherent_section_source_products.py` executes the 4374 original Jordan algebra product tests. Both PASSED. GitHub #52 and #1239 have matching owner-source standalone script `scripts/check_griess_M81_coherent_SL3_section_steelman_bidi.py` (independently designed compact solver) but the precise newly committed blob has NOT been byte-identically replayed in the local container.

**Formal repository implementation**:
- Lean #52 `Integration/Griess1990MoufangCoherentSL3Section.lean`: uses ACTUAL previous source `Loop81`, `phaseCorrection`, `centralCharacterShift`, six explicit outputs, checkable actual 81-automorphism multiplication, order3, source unit, selected Steinberg commutation/commutator, all six source-phase histograms 3,3,3 and selected actual J0 trace -1 vs grade26 trace8. Source-written, **NO Lean kernel toolchain run**; 5616-element group presentation/character irred theorem is currently an exact Python certificate, **NOT a kernel-verified Lean theorem**.
- Agda #1239 `DASHI/Moonshine/Griess1990MoufangCoherentSL3SectionSourceExact.agda`: DIRECTLY reuses the original Griess M81 grade/trit model and original g; defines the identical six elementary corrections and coherent automorphism maps, source reduction examples, and 81 source-written same-row commutation cases; **NO Agda kernel run**. No shadow octonion/VOA source.
- Source independent scripts added to BOTH existing PRs, with original authors, accepted/rejected claims and exact source roles.

## Adversarial negative: FULL Albert J0 is irreducible, grade26 is not

The same explicit section is a genuine source-defined linear algebra automorphism group of the original 27-dimensional Albert algebra. The native rational 27×27 map from earlier work transports this group to the ACTUAL native octonionic Jordan product, conditional on the previous independently checked 729 source→native basis witness.

For all **5616** section elements, enumerate the fixed original homogeneous grades `M x=x` and their actual ω phase weights to compute the rational 27D Albert trace. Remove its fixed original unit contribution 1 for trace on ACTUAL Albert J0=ker(tr), dim26. Independent *both symbolic-source and literal 81-point-permutation* group enumerations agree exactly:

| Tr_{J0}(g) | multiplicity |
| --- | ---: |
| 26 | 1 |
| 2 | 819 |
| 0 | 3132 |
| -1 | 1664 |

Classical character orthogonality gives
`(26²+819*2²+1664*1)/5616 = 1`. Therefore **the genuine 26D Albert J0 representation of THIS full coherent SL3 complement is absolutely irreducible over C** (and hence over Q). The corresponding 26-point nonzero-grade permutation action has character inner product **3** because it has precisely THREE original ordered-pair orbitals (equal, opposite, independent), with rational projectors of ranks 1+12+13.

Consequently **NO FULL SL3-equivariant linear identification exists between the original 26 nonzero-grade point permutation module and the genuine rational Albert J0**, for ANY of the 27 source-character-conjugate complements. This resolves the strongest positive and strongest negative versions:
- POSITIVE: previous ACTUAL rank26 rational intertwiner `B X=X P` for one source order13 C13 subgroup, explicit det `-729/4096` survives untouched.
- NEGATIVE: all 5616 coherent full-group actions on real Jordan J0 are irreducible, grade26 is reducible, and earlier selected lifts also have a one-generator character mismatch. The full-Jordan irreducibility is stronger and no longer relies on incoherent arbitrary shear selection.
- DIFFERENT structures: original P3³ path graph adjacency and its antipodal signed holonomy are not invariant under full source grade SL3; the exact C13 Reynolds retains 5/26 squared norm, full SL3 only 2/13 and annihilates odd13 signed graph operator. Neither physical quantum/KK/string mechanism nor Monster 3B selected-VOA mode can be claimed.

## The exact two-sided acceptance criteria and next Pareto

**PRODUCER / affirmative**: A candidate full-action mapping must construct a 5616-element same-source group section, verify all six 81-loop maps and 729 Jordan basis products each, and prove a conjugacy/intertwiner with an invertible explicit matrix. We HAVE the coherent section and verify ALL 4374 products computationally; no full grade26 equivariant intertwiner exists.

**ADVERSARIAL / negative**: prove the squared character inner products differ (1 vs3), using source-defined algebra operators not merely scalar dimensions. FULL finite evidence PASSED. It is not an assertion that no alternate 26-dimensional module, selected quotient or physical system can exist. Conditional no-go only for the specified grade26 permutation module vs Albert J0 under this coherent full source group.

**Remaining P0 kernel**: Lean/Lake actual execution of the original Griess homogeneous source→native 729 Jordan basis equality, all six source lifts/Steinberg relations, 5616-element exact group-order section and finite character orthogonality; Agda typecheck of actual M81 source model and reuse of original rational Albert transport. Toolchain unavailable in authoring environment; no CI/proof receipt invented. An actual Lean group action + irreducibility theorem is the NEXT deep formal producer if toolchain becomes available.

**P1**: cross-pollinate to genuinely source-selected VOA phase and existing F4 rational-form owners only with actual same-object intertwiner; do not conflate the Albert27 3³ grading, the native P3³ spatial graph, the Monster Moonshine Griess 196884D algebra, or the separate 240/243 E8 root-action no-go. Apply Agda #1267 source-first bidirectional severe-inquiry protocol: preserve positive steelman and independent negative discriminator; unresolved does not mean refuted and original provenance is not evidence of experimental physics.

## Status invariant

Published 1974/1976/1980/1990 original theorem ≠ later repository code ≠ exact locally run finite tests ≠ source-written Lean/Agda theorem ≠ proof assistant kernel certification ≠ observed physical phenomena. Give original authors direct, dated priority; group-theoretic character tests are classical; report local algorithmic contributions as subsequent DASHI/ChatGPT implementation; never promote structural resemblance into physical causation.


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
