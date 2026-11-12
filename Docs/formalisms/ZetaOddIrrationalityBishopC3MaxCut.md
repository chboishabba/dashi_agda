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
