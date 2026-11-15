# Odd zeta irrationality × Bishop × C3: source-preserving max-cut

## Attribution and scope

- **External mathematics:** Wadim Zudilin, *One of the odd zeta values from zeta(5) to zeta(25) is irrational*, arXiv:1801.09895. The July 2026 Lean/Mathlib manuscript supplied by the user reports the fallback window through zeta(33), using Hanson's elementary lcm bound. This is an external result, **not** an original DASHI theorem.
- **External formalization:** exact GitHub repository, revision, declaration, axiom list, and theorem-to-`riemannZeta` identification are **not yet admitted**. Do not describe a screenshot as a retrieved or kernel-checked source file.
- **Existing DASHI work:** `DASHI/Foundations/BishopGoldenRatioCarrierExact.agda` supplies a Bishop carrier for phi; `DASHI/Moonshine/QuadraticIrrationalSignedApproximationFibreExact.agda` keeps rational approximation separate from exact irrational targets; `DASHI/Analysis/RiemannAnalyticSubstrate.agda` specifies, but does not construct, the actual completed zeta analytic layer; `DASHI/Moonshine/C3RiemannConjugationBridgeExact.agda` proves a *coordinate* reflection/conjugation relation, not a zeta-zero theorem.
- **New DASHI contribution:** `DASHI/Analysis/ZetaOddValueWitnessTransportExact.agda` derives disjunctive irrationality transport along explicitly provided equalities in one selected value carrier, with preserved witness index. It does not supply the equalities.

## Max-cut dependency graph

```text
External Lean theorem at an exact revision [OPEN]
             |
             v
Lean's selected zeta definition -> actual positive-odd Dirichlet values [OPEN]
             |
             v
Lean values == Bishop values on same carrier [OPEN]
             |
             +-----> generic witness transport [CODE ADDED; TYPECHECK PENDING]
             |
             v
Bishop values == DASHI analytic substrate values [OPEN]
             |
             v
DASHI odd-zeta irrationality witness [CONDITIONAL]
```

The independent C3/xi conjugation and orbit-shape comparisons are not inferred from irrationality, and do not discharge RH Weil positivity.

## Proof ledger (no promotion without admission)

| Gate | Exact obligation | Status |
| --- | --- | --- |
| ZI00 | Inspect external Lean repository/commit, check theorem statement, `#print axioms`, and provenance | OPEN |
| ZI01 | Match the 15 argument indices `5 + 2*k`, `k : Fin 15` to the external finite set | OPEN |
| ZI02 | Identify Lean real/complex zeta values with selected Bishop-real values | OPEN |
| ZI03 | Identify Bishop-real values with genuine DASHI analytic zeta values | OPEN |
| ZI04 | Preserve an existential irrationality witness along explicit equality | IMPLEMENTED, NOT TYPECHECKED |
| ZI05 | Verify direct vs via-Bishop commutation on the same witness index | IMPLEMENTED, NOT TYPECHECKED |
| ZI06 | Ingest source provenance and proof dependencies into canonical world admission | OPEN |
| ZI07 | Integrate genuine accepted theorem into public `ZetaTheoremSurface` | BLOCKED ON ZI00–ZI03 |
| ZI08 | Evaluate reusable Stirling, factorial, LCM and rational-separation lemmas against Bishop/golden-ratio approximation libraries | OPEN |
| ZI09 | Preserve C3 orbit-shape non-identification and RH/Weil analytic gates | MAINTAINED BOUNDARY |

## Golden-ratio and irrational-number cross-pollination

The relevant transferable design pattern is not equality of phi and odd zeta values. It is:

1. Rational presentations/finite approximations must not be confused with an irrational analytic target.
2. Embeddings and actual value equalities carry theorem transport, not matching names, decimal approximations, or abstract isomorphism.
3. A signed approximation defect, a lower bound, or an algebraic minimal polynomial is evidence for its *own selected value*, not for unrelated zeta values.
4. Reuse exact proof objects and source identities through fibres/provenance; do not duplicate carrier definitions or hide imported hypotheses.
5. The golden ratio is algebraic irrational; irrationality alone does not characterize an odd zeta value or establish transcendence.

## Verification protocol

No repository-local Agda compiler is available in the current execution environment. Run the repository's pinned Nix/Agda environment (not a generic latest Agda) and type-check the new module with the established include paths. Do not label ZI04/ZI05 'machine-checked' until successful. Then add a source-pinned external Lean artifact and separately discharge ZI01–ZI03.

## Attribution references

- W. Zudilin, arXiv:1801.09895: https://arxiv.org/abs/1801.09895
- Existing exact phi carrier: `DASHI/Foundations/BishopGoldenRatioCarrierExact.agda`
- Existing rational-approximation fibre: `DASHI/Moonshine/QuadraticIrrationalSignedApproximationFibreExact.agda`
- Genuine zeta boundary: `DASHI/Analysis/RiemannAnalyticSubstrate.agda`
- C3 coordinate boundary: `DASHI/Moonshine/C3RiemannConjugationBridgeExact.agda`

## Additional candidate external proof (not admitted)

The public `telaviv/zeta-irrationality` README reports an unconditional Mathlib theorem `ZetaIrr.Z7.oneOfZeta7To21` proving that one of zeta(7),...,zeta(21) is irrational, with exactly `[propext, Classical.choice, Quot.sound]` as reported axioms. URL: https://github.com/telaviv/zeta-irrationality . Its actual commit and source declarations have not been fetched or checked here. As the set {7,...,21} is a subset of {5,...,33}, an eventual verified witness can map into the existing 15-index `OddWindow`, but a proper finite-index embedding theorem is still necessary (ZI01).

The separate 2026 individual zeta(5) projects must not be treated as automatically interchangeable. For example, https://github.com/danromik/zeta5-irrationality reports a prime-number-theorem axiom, whereas https://github.com/long-mathematics/zeta5-irrationality explicitly says it has not yet proved the endpoint. Verify every project's own trust boundary before admitting a claim. These are external projects; no credit is transferred to DASHI.

## RH Clay rollup integration — independent proof owners

The exact RH source owner `DASHI/Analysis/RiemannMillenniumAssembly.agda` composes a *supplied* `DashiRiemannAssembly` into `RiemannHypothesisFor`. Its prerequisites are the actual analytic substrate, compatible explicit formula, DASHI/Weil exact identification, positivity/dense extension, and criterion. The newer `DASHI/Analysis/RiemannHermitianSourceGapMapExact.agda` exposes G1 complex Poisson, G2 mixed kernel, G3 normalized Hermitian excess and G4 error-floor-closer gaps. `RiemannHermitianEndgameTrichotomyExact.agda` admits localization/higher-moment/arithmetic-rigidity only with a genuine closer.

Added `DASHI/Analysis/RiemannOddIrrationalityClayBoundaryExact.agda`:

- `jointEvidenceYieldsOddDashi`: obtains the odd-value consequence from the supplied odd-value certificate *and both value equalities*.
- `jointEvidenceYieldsRH`: obtains RH from the separately supplied `DashiRiemannAssembly`, not from odd irrationality.
- `genericOddWitnessCannotForceOffLineExclusion`: a finite Boolean **abstract-interface countermodel** to the invalid inference from an arbitrary odd-irrationality witness to excluding independent off-line states. This is explicitly not a counterexample to the actual Riemann hypothesis.

Proposed RH-specific integration gate `ZI10`: identify the selected odd-value DASHI analytic carrier with the same `AnalyticSubstrate` used in the terminal RH assembly. This shares value provenance, not proof strength. `ZI10` remains OPEN.

### Active Clay leaves (do not collapse into ZI04)

1. Actual completed-zeta / xi analytic layer and exact prime-zero formula, including Gamma/pole/trivial-zero terms.
2. Real DASHI arithmetic observable identified with the full von Mangoldt-weighted prime side (not unweighted `p*v_p(n)`).
3. One genuine Weil positivity route: exact coercivity plus density, or global decomposition.
4. Hermitian alternative G1–G4 if chosen: complex Poisson, mixed-kernel summation, normalized excess, and a strict bound above the second-moment error floor.
5. Separate source-exact Lean RH Clay statement/criterion weld, and terminal kernel-admission check; no signed-inequality margin is inferred from positive-odd zeta values.

### Verification boundary

Both new Agda files are source-written, committed, readback-verified, but **not kernel-checked** in this session. No Nix/Agda executable was available locally. Consequently no claim that `ZI04`, `ZI05`, or the Clay countermodel is a machine-checked theorem should be made until the repository's pinned check passes.

## 2026-11-12 recent Bishop PR audit: replace outdated dependency picture

**PR #1478 (Agda)** https://github.com/chboishabba/dashi_agda/pull/1478, 80 changed paths. Source-level owners include:
- `DASHI/Analysis/BishopComplexExpFactEqualsNativeExpExact.agda`: literal complete factorial complex series to the selected native Bishop complex exponential. Its own header says source-written, **NOT Agda kernel verified**.
- `DASHI/Analysis/BishopComplexCauchyTriangleLimitTransportExact.agda`: coordinatewise square/rectangle -> Cauchy triangle limit using original wings and vanishing differences.
- `DASHI/Moonshine/AbelBishopOriginalComplexCarrierWeldExact.agda`: explicit bidirectional record conversion, preserves original Bishop-real re/im and setoid equality, with multiplication/addition compatibility.
- Additional finite binomial, rectangle, triangle-tail, signed factorial, complex log, Koenigs and Machin source modules. These are meaningful internal prerequisites already source-written; don't duplicate them.

**PR #104 (dashi_lean4)** https://github.com/chboishabba/dashi_lean4/pull/104, 9 changed paths. Its actual patches contain:
- `Integration/BishopNegativeLogNativeRound11Semantics.lean`: selected literal negative-log source finite partial sums, convergence and faithful evaluation, including `canonicalNegativeLog_converges`, `anyOriginalNatSuccessorExpInverse`.
- `Integration/BishopPureImaginaryInfiniteCauchyProductExact.lean`: absolutely summable factorial coefficients and full infinite Cauchy product.
- `Integration/BishopRound11ImaginaryProductSemanticReflection.lean`: source-backed sine/cosine addition and Machin-quarter semantic setoid reflection.
- **`Integration/BishopRiemannZetaNativeMachinContinuity.lean`** already provides `originalDirichletTerm_eq_cpow`, `originalDirichletValue_eq_riemannZeta (hs : 1 < s.re)`, `originalDirichletValue_continuousAt`, `completedRiemannZeta_continuousAtMachinPi`. This is the genuine Mathlib zeta on the half-plane, NOT an opaque zeta-like function.
- `Integration/AxiomAuditMoonshineRound11RouteB.lean` adds `#print axioms` calls for key exact theorem names; the presence of audit commands is **not** evidence of their output or successful build.

### Updated minimum cut, with same-value ownership

- **ZI-L1 (already source-written on Lean PR #104):** positive-half-plane classical Dirichlet coefficient and infinite sum equal Mathlib `riemannZeta`; test and kernel/axiom audit still need run evidence.
- **ZI-L2 (new minimum):** instantiate the external odd-zeta irrationality proof on the *same* `riemannZeta` with precisely typed `5+2k` indices; avoid an unnecessary second zeta representation.
- **ZI-A1:** transport that Mathlib value through PR #104's actual vendored `RegularRatReal` faithful `eval`/equivalence into the independently selected original Agda Bishop `Real.ℝ`. This is not yet a cross-kernel proof.
- **ZI-A2:** construct an explicit `ZetaHalfPlaneLayer` and source identity on the Agda side; the current `RiemannAnalyticSubstrate` is an interface, so no full actual analytic function is automatically obtained.
- **ZI-RH:** tie to the genuine selected `AnalyticSubstrate` of `RiemannMillenniumAssembly` without inferring Weil positivity, off-line exclusion or RH from positive-odd irrationality.

**Correction to earlier framing:** we do *not* need to build a complex exponential or prove a Mathlib half-plane Dirichlet equivalence from scratch. They exist as source-level modules in the recent PRs; remaining hard work is verifying their compilation/axioms and identifying cross-kernel original objects. The golden-ratio fibre remains reusable evidence-transport/approximation infrastructure, not a zeta-value identity.

This audit is based on connector-retrieved PR changed-file lists and file patches, **not claimed current CI or kernel-build results**.

## 2026-11-12 positive-odd specialization implemented in Bishop Lean PR #104

New `Integration/BishopOddZetaHalfPlaneSpecialization.lean` committed to `chboishabba/dashi_lean4` PR #104 branch, commit `b18d8d05a7aa04339c97debca03e9fab595f2d3f`:
- `oddArgument_gt_one`: every `5+2*k` lies in `Re(s)>1`.
- `originalOddDirichlet_eq_riemannZeta`: specializes existing `originalDirichletValue_eq_riemannZeta` without introducing a new analytic object.
- `originalOddWindow_eq_riemannZeta`: `Fin 15` same-object equality.
- `oddWindow_rational_iff`, `oddWindow_irrational_iff`: pointwise transport of the explicit existential `HasRationalComplexValue` predicate.
- `zetaOddWindow_exists_iff_sourceWindow`: finite-window existential transport in both directions.
- Two `#print axioms` probes (execution evidence still missing).

**Precise scope:** the rationality predicate is `∃ q : ℚ, z = (q : ℂ)`. This must still be welded to the external proof's *actual* definition of irrationality (often on `ℝ`, or an odd zeta value seen through complex coercion). Neither the external disjunction nor native Agda carrier equality is imported. This is therefore source-written, not a kernel-verified closure of ZI00, ZI01 or ZI03.

Next cut: after the pinned Lean build, obtain the external theorem's exact Lean declaration and specialize its genuine Mathlib zeta to this finite window, proving the rationality predicate equivalence. Then settle the Agda/Bishop semantic evaluation boundary. The completed RH assembly remains wholly independent.

## 2026-11-12 narrower-window real/complex exact transport

Public external source: Shawn Krisman, `telaviv/zeta-irrationality` at https://github.com/telaviv/zeta-irrationality ; README declaration `ZetaIrr.Z7.oneOfZeta7To21 : OneOfZeta7To21`, where `OneOfZeta7To21` is a finite-set existential over `Irrational (riemannZeta j).re` for `j ∈ {7,9,...,21}`. Source README reports a kernel audit `[propext, Classical.choice, Quot.sound]`; this report is external, not independently rerun. The README attributes mathematical lineage to Ball–Rivoal, Rivoal, Zudilin and Lai–Zhou, with the Z7 construction based on Zudilin's 2004 work and a distinct pole-block profile. It additionally declares AI-generated implementation and no independent human mathematical audit; preserve both qualifiers.

DASHI Lean PR #104 branch gained `Integration/BishopOddZetaNarrowWindowTransport.lean`, commit `14b175ca16a1c63202a383f9e92e0739bbb40dde`. The new source proves (subject to pinned Lean compilation):
- `irrational_real_iff_no_rational_complex`: Mathlib real irrationality iff exclusion of a rational complex cast;
- `irrational_re_iff_complex_rational_neg`: the same for complex `z` with explicit `z.im=0`;
- `intoFifteen` and `intoFifteen_same_argument`: `Fin 8` -> `Fin 15` preserving `7+2k=5+2(k+1)`;
- `narrowerWitness_to_originalSource`: transport an externally **supplied** Z7-style real irrationality witness to the existing original Bishop/Dirichlet source window, given real-valuedness of positive-odd Mathlib zeta. Neither the existential theorem nor real-valuedness is postulated as a global axiom.

Still open: pin and read the external theorem declaration and exact commit, prove finite-set -> `Fin 8` witness conversion, discharge positive-odd zeta imaginary-part zero by an actual Mathlib theorem, run pinned Lean kernel and axiom audits, and transport into the original Agda Bishop carrier. Cross-version Lean 4.35 external vs existing project compatibility is a *version-change proof surface*, not permission to identify snapshots without inspection.

No information here settles the RH Clay Weil-positivity or G1–G4 error-floor gates.

## 2026-11-12 evening: physical source-admission implementation and corrected mathematical cut

### New source-written proof surfaces

**Lean PR #104** (existing branch `feat/bishop-k04d-k05-source-semantics-20261103`):
- `Integration/PositiveOddZetaImaginaryZeroExact.lean`: `riemannZeta_nat_eq_real_tsum`, `riemannZeta_nat_im_zero`, `positive_odd_zeta_im_zero`, `z7_eight_window_im_zero`, `fifteen_window_im_zero`, `originalDirichlet_fifteen_window_im_zero`. The proof uses the actual Mathlib `zeta_nat_eq_tsum_of_gt_one` and `Complex.ofReal_tsum`, hence no hypothetical uniform-limit continuity assumption.
- `Synthesis/PositiveOddZetaImaginaryZeroExact.lean`: exact re-export into the requested Synthesis tree.
- `Integration/BishopOddZetaZ7FinsetBridgeExact.lean`: literal external **statement-shape** `{7,9,11,13,15,17,19,21}`, Finset -> Fin 8, Fin 8 -> Fin 15, unconditional removal of the old positive-odd `im=0` *hypothesis*, but not import of the external theorem proof.
- `Integration/RiemannXiMathlibReflectionExact.lean`: `selectedXi(s)=(s(s-1) completedRiemannZeta₀(s)+1)/2` and `selectedXi(1-s)=selectedXi(s)`, using Mathlib's actual entire completed-zeta `completedRiemannZeta₀_one_sub`. `selectedXi(0)=selectedXi(1)=1/2`. The selected Lean xi is not a constructed instance of Agda's `AnalyticSubstrate`.
- `scripts/check_bishop_odd_zeta_maxcut_local.sh`: Nix/native local check entrypoint; fails closed on an observed root version-pin mismatch, without a CI dependency.

**Version-isolated external proof import in Lean PR #104**:
- `proofs/zeta7-lean435/lean-toolchain` selects Lean v4.35.0;
- `proofs/zeta7-lean435/lakefile.toml` requires `ZetaIrrational` at external tag `v1.0` (its manifest pins Mathlib v4.35.0);
- `proofs/zeta7-lean435/BishopZ7Admission.lean` **imports the actual external theorem** `ZetaIrr.Z7.oneOfZeta7To21`, transports the finite set to `Fin 8` and the existing fifteen-window shape, and produces (conditional only on any NEW source-value equality) a non-rational value on that same source carrier. The genuine Mathlib odd-zeta witness in this separate v4.35 sidecar is unconditional *provided the imported external theorem builds as documented*.
- `proofs/zeta7-lean435/check_local.sh`: build and `#print axioms` verification using native Lake, not Docker or CI.
- The root `dashi_lean4` project's `lakefile.toml` currently requests Mathlib **v4.28.0**, while its `lean-toolchain` reads **v4.35.0-rc3**. These observed pins do NOT match the external stable v4.35.0 project. No binary theorem import across them is claimed. Version compatibility is an explicit gate.

**Agda PR #1497**:
- `DASHI/Analysis/ZetaZ7AgdaIndexTransportExact.agda`: eight literal constructors for 7,9,...,21; proofs of all eight `Odd.oddArgument` equations; conditional source-index/irrationality transport to the existing `Odd.ValueContext`; witness index preserved without inventing a numerical chosen value.
- `scripts/check_zeta_odd_bishop_rh_local.sh`: local Nix/Agda 2.9 check using the already established `scripts/run_agda29_parallel_check.sh` against the three Agda Z7/Bishop/RH boundary modules.
- All new files are **source-written and GitHub-readback candidates until a local Lean/Agda kernel run succeeds**; scripts have not been executed in this session. No CI status is substituted for a local run.

### Corrected ledger

| Gate | Precise status after implementation |
| --- | --- |
| ZI reality | Mathematical proof written for actual Mathlib zeta; local Lean checker PENDING |
| ZI external Z7 import | Actual external `ZetaIrr.Z7.oneOfZeta7To21` imported in isolated stable-v4.35 sidecar; sidecar kernel/axioms PENDING |
| ZI Finset membership to Fin8, to Fin15 | Source-written in both sidecar and Agda index carrier; kernel PENDING |
| ZI value to original Lean Dirichlet series | Prior Bishop Lean PR #104 source equality, specialized across 15 values; kernel PENDING |
| ZI original Agda Bishop-real same-object weld | OPEN: a faithful cross-kernel semantic interpretation is not the same as renaming `RegularRatReal`, and no verified proof term crosses Lean to Agda |
| Xi reflection G1 (selected Mathlib xi) | Reuses actual `completedRiemannZeta₀_one_sub`; specialized source lemma written; kernel PENDING |
| Xi reflection G1 (original Agda analytic substrate) | OPEN: the abstract `CompletedRiemannZeta` package does not yet have a genuinely constructed same-object instance |
| RH G2 | OPEN: real prime-power / gamma / pole / zero explicit-formula identity and exact observation operator, not the 3-adic label analogy |
| RH G3 | OPEN: coercivity or an analytic off-line zero-exclusion estimate that beats the genuine error floor; the proposed signed-fifth and far-shell bounds are NOT source-certified closures |
| RH G4 | OPEN: complete `RiemannHypothesisFor` witness; conditional terminal assembly in source is not an inhabitant |
| YM Wilson P0 scalar weld (separate Clay programme) | OPEN: `YMClayP0BishopToOriginalWilsonRealWeldExact.agda` explicitly leaves `OriginalWilsonToBishopScalarWeld` uninhabited, because the selected original `RealAnalysisAxioms.ℝ` differs from the vendored Bishop real `Real.ℝ`. Bishop quotient cancellation alone cannot construct a faithful map and reflection from an independent postulated scalar socket |
| Local kernel receipts | NOT RUN: this runtime has no `lake`, `lean`, `agda` or `nix`; local native scripts now identify exact targets |

### Mathematical non-promotion controls

1. The **true Z7 window** is `7..21` over odd integers, mapping into `5..33` at indices `1..8`, **not** a window `17..31`.
2. `∃ j, Irrational(ζ(j).re)` permits *proof-theoretic existential elimination*, not a computed single named irrational value or a modulus `δ(q)` for a known index.
3. An im=0 proof at positive integer arguments does not imply analytic continuation, RH, or uniform Bishop-real equality. The direct Lean proof is simpler than a free abstract modulus.
4. The classical completed-ξ identity and functional reflection do not exclude off-critical-line zeros; the full Weil/Poisson/Selberg/Hermitian analytic positive route remains unpaid.
5. The constructive Bishop inverse uses apartness of the **selected** denominator, not a bare rational sequence inverse at arbitrary early cutoffs; the independent original Wilson scalar still needs an operation-/equality-/order-preserving interpretation.
6. Keep theorem lineage separate: external Zudilin/Ball–Rivoal/Rivoal/Krisman mathematical and Lean formalization work; Mathlib zeta and completed-Lambda owners; original Bishop/Murray/Csimma real construction; DASHI's exact integration and source-index transport.

## 2026-11-12 Setoid and original Wilson partition max-cut — source implementation

### Reuse of prior actual Cauchy-completion work

Existing master owners `BishopFastCauchyRealEquivalenceExact`, `BishopFastCauchyCommonCompletionExact`, and `BishopFastCauchyCategoricityInstanceExact` already define the Bishop ↔ FastCauchy conversion, canonical rational-approximation bridges, and conditional setoid equivalence. These are **not inhabited** merely because the two carriers describe rational sequences. Bishop regular sequences and dyadic FastCauchy representatives have different precision indexing; rational reindexing, round trips, and operation preservation must be proved.

New `DASHI/Analysis/BishopSetoidWeldExact.agda` proves source-level, generic exact lemmas for any **supplied** `Spine.SetoidRealEquivalence` and verified rational-embedding agreement:
- `rationalAgreementBackwards`: the inverse rational source agreement follows from the existing round-trip proof;
- `rationalLeftToRight` and `rationalRightToLeft`: preserved and reflected rational-image predicates;
- `irrationalLeftToRight` and `irrationalRightToLeft`: bidirectional irrationality transport without decidability of irrationality;
- `irrationalRightCongruent` and `existentialIrrationalityTransport`: selected-value equivalence and existential witness preservation.

New `DASHI/Analysis/BishopFastCauchyZetaWeldExact.agda` specializes the generic layer to the **already-selected** `Canonical.bishopFastCauchyCanonicalEquivalence`, constructs `makeRationalWeld` from an *explicit* rational agreement, and transports an actual fifteen-value witness only with an *explicit* same-source value comparison.

**Unpaid original input:** instantiate the existing `BishopFastCauchyCategoricityData` from real rational-reindexing and source convergence proofs, then provide actual source-specific `Mathlib/Lean ↔ Bishop` evaluation and `Bishop ↔ Agda RiemannAnalyticSubstrate` value equality. Neither construction follows from an interface having a name. This change does NOT inhabit the common-completion records; it proves the value/witness transport *after* the real equivalence.

### Original Wilson finite partition: branch owner PR #1444

The independent Wilson source `RealAnalysisAxioms.ℝ` is a postulated propositional-equality carrier; Bishop's vendored `Real.ℝ` has setoid equality. The Wilson scalar type is NOT `FastCauchyReal`, and neither Bishop/Fast equivalence nor strict partition positivity identifies them.

New `DASHI/Physics/YangMills/YMClayP0OriginalPartitionBishopApartnessExact.agda` on PR #1444 specializes the already-owned original source:
- `originalPartitionPositive`: consumes `YMClayOriginalWilsonFiniteNumeratorOrderExact.originalWilsonPartitionStrictlyPositive` for the *same* finite Wilson Gibbs/Haar partition;
- `partitionImagePositive`, `partitionImageApartZero`: obtain a genuine Bishop positive order/apartness witness through the **supplied** `OriginalWilsonToBishopScalarWeld`;
- `selectedBishopPartitionInverse`, `partitionImageQuotientCancellation`: use Bishop's native constructive inverse and P0 cancellation lemmas;
- `originalWilsonPositiveDivideCancellation`: applies the existing exact source Wilson quotient law **under the same supplied scalar weld**.

**Unpaid original input:** construct `OriginalWilsonToBishopScalarWeld divide` or replace/reinstantiate the original Wilson consumer over a constructed Bishop quotient with an explicit semantics-preserving comparison. Positivity is already witnessed and does NOT inhabit the independent interpretation.

**Correction to a tempting but invalid shortcut:** `exp(-beta * numberOfPlaquettes)` is in general a positive *real*, not a positive rational `q₀`. A finite-action uniform lower bound also needs actual trace bounds, nonnegative beta, exponential monotonicity and normalized Haar monotonic integration for the same chosen action. Such an inequality is unnecessary for apartness once the original strict partition positivity witness is available.

### RH Gate G2/G3/G4 distinction

The user's displayed prime/zero trace is schematic, not an admitted genuine Weil explicit formula: the classical explicit formula includes normalization, poles/trivial zeros and archimedean Gamma contributions depending on the Fourier/test-function conventions. Similarly, positive-definiteness on the real Fourier axis does not alone establish a sign contradiction for every off-line zero. The missing analytic test-function separation and **uniform** Weil positivity remain the substantive Clay obstruction.

Selected Mathlib `completedRiemannZeta₀_one_sub` can prove the **functional equation** of the genuine entire xi. The new Lean `selectedXi_eq_classical_completed` source identifies `(s(s-1)Λ₀(s)+1)/2` with the classical `s(s-1)Λ(s)/2` away from s=0,1 via the actual Mathlib `completedRiemannZeta_eq`. This does not inhabit the independent Agda `AnalyticSubstrate` and does not assert RH.

### Verification and exact status

- Source-written / GitHub-committed: two new Agda setoid files on PR #1497; one Wilson partition file on PR #1444; Mathlib xi identity extension on Lean PR #104.
- Local check targets updated: `scripts/check_zeta_odd_bishop_rh_local.sh` on PR #1497; new `scripts/check_ym_bishop_partition_maxcut_local.sh` on PR #1444. No Docker or CI dependence.
- Local Agda/Lake/Nix kernel output: **NOT OBSERVED** in this execution environment. These source-written statements are therefore **NOT promoted to machine-checked**.
- Substantive open gates: concrete Bishop ↔ Fast rational Cauchy reindexing and categoricity inputs; original Wilson postulated scalar interpretation; actual Agda-vendored zeta same-value analytic construction; true Weil positivity/RH G2–G4.

**Attribution:** external work belongs to Bishop/Bridges, Murray/Csimma, Geuvers/Niqui, the Mathlib zeta contributors, and Zudilin/Ball–Rivoal/Krisman's formalized theorem respectively. The novel DASHI commits in this iteration are the selected-value proof transport and original finite Wilson apartness specialization; they are not new proofs of the external analytic or millennium results.

### Precise rational-representation normalization follow-up

The concrete FastCauchy metric authority in `DASHI/Analysis/CanonicalRationalMetric.agda` uses the standard library's **reduced** `Data.Rational.Base.ℚ`, while the vendored Murray/Csimma Bishop `Real._⋆` embeds **unnormalised** `Data.Rational.Unnormalised.ℚᵘ`. This rules out claiming literal representation identity between their source rational sequences.

- `BishopFastCauchyZetaWeldExact.makeRationalWeld` now fixes its rational carrier to the real original `ℚᵘ` and left embedding to `Real._⋆` (rather than accepting an arbitrary set as "Rational").
- New `BishopFastCauchyCanonicalRationalWeldExact.agda` defines `canonicalFastFromBishopRational q = CanonicalRationalMetric.canonicalRationalEmbedding (Data.Rational.Base.fromℚᵘ q)` and proves by definition that every finite FastCauchy term equals that reduced rational; its `canonicalRationalWeld` consumes the same **still pending** original Bishop/Fast categoricity and rational source agreement.

Thus the original normalization map and finite constant-rational embedding are source-written/precisely selected, but canonical equivalence on all Bishop sequences, original series values and RH analytic substrate is **NOT** thereby proven. No local Agda kernel acceptance has been observed.

## 12 November new upstream source paydown — verified PR metadata, not kernel proof

Agda Bishop [PR #1478](https://github.com/chboishabba/dashi_agda/pull/1478) now additionally owns:
- `AbelBishopLogQuadraticUpperDiskSeriesLimitExact`: original shifted log series converges on actual closed upper-radius disks, with its limit the original canonical log minus the linear term. Does not require the false same-radius equality.
- `AbelBishopSelectedLogUpperDiskQuadraticTailExact`: exact 2/27 p⁻¹t chart specialization with genuine selected upper-disk inequality.
- `AbelBishopLogQuadraticUpperDiskHalfGeometricExact`: actual half-coefficient Bishop comparison yields componentwise ABSOLUTE convergence of original shifted log terms and identifies the resulting limit with the same canonical remainder.
- `AbelBishopLogUpperDiskZeroNormalizationExact`: upper-disk log(1)=0 from same-term series convergence and uniqueness.
These are K04d/Koenigs source donors, **not** an Agda Dirichlet/zeta identification. Norm-square-proportional remainder `|R₂| ≤ 8/27|t|²`, actual Newton orbit analytic inputs, principal inverse, local/global Koenigs are still mathematically open. Source readback only, local Agda kernel pending.

Lean Bishop [PR #104](https://github.com/chboishabba/dashi_lean4/pull/104) now additionally owns `proofs/zeta7-lean435/BishopZ7DirichletSameObject.lean`. In the version-isolated stable-v4.35 Mathlib workspace, this explicitly defines the complex Dirichlet `∑' n, 1/(n+1)^s`, proves **the literal same-value equation** with Mathlib `riemannZeta` on Re(s)>1, and composes that equation with the external imported Z7 witness to obtain a fifteen-odd-value existential result. This pays one genuine single-version Mathlib selected source-value equality and avoids the root Lean/Mathlib pin mismatch. The sidecar local checker now includes strict per-theorem axiom-whitelist parsing. No local Lake/kernel acceptance was performed.

**Still highest-alpha for this ZI ledger:** (1) verify stable-v4.35 source and exact axioms locally, (2) instantiate the original Agda Bishop-real analytic zeta at the same values, including real/complex rationality reflection and faithful cross-prover interpretation, (3) complete Bishop/FastCauchy canonical reindexing/round trips and a same-value series-limit comparison, (4) independently prove RH explicit-formula/Weil positivity and hermitian G1–G4. No cross-prover proof imported merely by mirroring declarations.

## 2026-11-13 focused eight-gate continuation: concrete original source proofs vs open math

### P1.L and Koenigs donor: Agda Bishop PR #1478

New `AbelBishopLogQuadraticSourceNormFactorExact.agda` source targets `originalBishopQuadraticSourceTermFactor`, `originalBishopQuadraticSourceNormSquare`, `originalBishopShiftedCoefficientSquareBelowQuarter`, `originalBishopQuadraticSourceNormSquareUpper`: the exact ORIGINAL coefficient `(-1)^(n+1)/(n+2)·w^(n+2)` factors through `w*w), and its true norm-square is bounded by `(1/4)*N(w)^(n+2)`. This uses existing `Norm.normSqScale`, `Norm.normSqPower`, literal signed coefficient and Bishop real monotonicity. It does not discard actual `N(w)` for the selected chart radius.

New `AbelBishopLogUpperDiskSetoidZeroExact.agda` source targets same-original-term convergence to zero when `w ≈C zeroC`, via original zero stream, finite series extensionality, Bishop convergence transport, and uniqueness, then selected affine chart center normalization `p + logSeries(p⁻¹·0) ≈C p`. Does not infer principal exp/log inverse.

Both registered in PR #1478's **91-unique-target** `scripts/check_analytic_j_tetration_golden_local.sh` (count is target registrations, NOT passes). Repo source readbacks and dependency symbol existence checked; local Agda 2.9 **NOT RUN**.

**Remaining true P1.L mathematical producer:** original Euclidean complex norm finite-sum triangle/limit-order inequality for the same shifted source terms, including `N(w)` rather than radius only, yielding `|R₂(w)| ≤ |w|²/(2(1-|w|))` and then the exact selected `8/27` coefficient. The new termwise norm-square bound does not imply a bound for the sum of complex terms without a triangle/Cauchy inequality and passage to the limit. P1.N native Taylor enclosures, squared contraction and exp/cos/sin orbit continuity remain unproved; local Koenigs still requires actual fixed-point source and analytic branch/univalence; global Kneser remains genuine mathematics.

### Rational carrier constructor: this Agda PR #1497

New `DASHI/Analysis/BishopFastCauchyRationalNormalizationRoundTripExact.agda` explicitly consumes standard-library `Data.Rational.Properties.fromℚᵘ-toℚᵘ` and `toℚᵘ-fromℚᵘ`:
- `reducedRationalRoundTrip : fromℚᵘ(toℚᵘ r) ≡ r`;
- `unnormalisedRationalRoundTrip : toℚᵘ(fromℚᵘ q) ≃ᵘ q`;
- `bishopRationalEmbeddingNormalization`: lifts original unnormalised equality through `Real._⋆` and `RealProperties.⋆-cong`;
- `canonicalFastReducedTermRoundTrip`: every term of the original FastCauchy **constant rational representative** is exactly the selected reduced rational.

This pays the concrete **rational normalization and constant-sequence** round trips, not the entire Bishop ↔ FastCauchy categoricity: the old `BishopFastCauchyCommonCompletion` takes arbitrary regular/dyadic sequence reindexing, generated maps, round-trip, field-law and completeness evidence. It also contains weak `Set` placeholders; these are not genuine proof receipts and must not be confused with a constructed canonical equivalence. Full reindexing and original zeta same-value series remain OPEN.

### Lean Z7 admission

Lean PR #104 now registers BOTH `BishopZ7Admission` and `BishopZ7DirichletSameObject` in its isolated stable-v4.35 `lakefile.toml` default targets, so the native `check_local.sh` can build each and run its strict `#print axioms` parsing. The actual external `ZetaIrr.Z7.oneOfZeta7To21` theorem is in external `ZetaIrrational/Statement.lean` + `Z7/MainUnconditional.lean`; the identical finite set is `{7,9,11,13,15,17,19,21}`. The sidecar uses genuinely selected Mathlib `zeta_eq_tsum_one_div_nat_add_one_cpow`. There is still **NO observed local Lean build** or cross-kernel Agda same-object zeta construction.

### YM and RH fail-closed endpoints

Yang--Mills original `DASHI/Foundations/RealAnalysisAxioms.agda` declares `ℝ : Set` and original algebraic operations by `postulate`. Its `OriginalWilsonToBishopScalarWeld` is therefore NOT constructible just by proving Bishop arithmetic or positive partition function; source interpretation or whole-consumer reparameterization must be supplied. PR #1498 only constructs conditional literal evaluator endpoints and independent **auxiliary free** Wilson denominator enclosures; four physical Wilson/ghost/Haar integrals and errors remain open, as do continuum E1/D1/D2/N1/G1.

RH Mathlib xi functional reflection and real half-plane zeta value identification do not supply the genuine prime-power-plus-archimedean Weil explicit formula **for the selected original Agda substrate**, nor positive quadratic trace for every admissible test, nor strict G3 compensating signed estimates. G2–G4 stay genuine open analytic/theorem-proving problems, not file or scalar welds. No RH proof claimed.

### Receipt discipline

- Source created/updated and exact GitHub branch readback: **YES** for named new modules.
- Static symbol existence / no explicit holes check: **YES** for new Bishop files, not equivalent to elaboration.
- Native pinned Agda 2.9, Lean 4.35 or Nix run: **UNAVAILABLE here**; zero new kernel-accepted receipts.
- User retains local golden checker authority; no CI success inferred; no Docker used.
