# Bishop K04d/K05 same-object max-cut — 2026-11-03

## Objective and evidence boundary

Close the **original** Bishop negative-log / Round11 signed-factorial / Riemann Dirichlet / Machin-pi obligations without introducing a second carrier, theorem-shaped `Set` placeholders, a classical proof imported without semantic equality, postulates, or fabricated kernel receipts.

Repository audited: `dashi_agda` at draft PR #1408, branch `feat/twin-prime-six-wheel-bounded-gap-reuse-20261028` (prior head `9cdde518e7d06d9e06c645829dbbae9f0124c862`); `dashi_lean4` is a companion, **not** evidence of Agda same-object kernel acceptance. Existing Agda modules in the table were read at that branch. This pass **did not run Agda**; no source-written item is promoted to machine-checked.

## Direct source audit, actual ownership

| Node | Reused source theorem owner | Actual status |
| --- | --- | --- |
| Real exponential addition | `Foundations/BishopExponentialCauchyProductExact.agda`: `bishopExpAdd`, `bishopExpTimesNegativeIsOne`; finite triangle/rectangle/wing owners | Existing *source-level* concrete Bishop-real law. Do not reprove. |
| Negative exponential order | `Foundations/BishopNegativeExponentialGlobalUnitIntervalExact.agda` | Existing source-level global unit-interval law. Does **not** identify exp(log n). |
| Convergent canonical negative log | `Foundations/BishopNegativeLogGeometricSourceConvergenceExact.agda`: `sourceNegativeLogValue`, `sourceNegativeLogMonotone` | Convergence/monotonicity written; the inverse of **this** series is a distinct open lemma. |
| Concrete Round11 log selection | `Analysis/BishopRound11CanonicalNegativeLogSameObjectExact.agda`: `canonicalNatLogIsOriginalBishopSum`; `Analysis/BishopRiemannDirichletExponentialTermExact.agda`: `originalNatLogAtOneExpIsOne`, `originalNatLogInverseFromPositiveSuccessors` | Canonical dataset/interval/zero index are written. Only positive successors require the genuine exp/log inverse; no arbitrary selected logarithm identification. |
| Mixed signed-factorial Cauchy | `Foundations/BishopExponentialCauchyProductExact.agda`; `Analysis/BishopSetoidComplexExact.agda`; `Analysis/BishopRound11ImaginaryProductPythagoreanReuseExact.agda` | **OPEN:** real exponential product alone does not prove `Round11ImaginaryExpMultiplicative` on the exact signed sine/cosine series. |
| Pythagorean, modulus, sine/cosine addition | `Analysis/BishopRound11ImaginaryProductPythagoreanReuseExact.agda`: `round11PythagoreanFromImaginaryProduct`, `round11ModulusFromImaginaryProduct` | Their dependence on one mixed Cauchy law is written. Do not list Pythagorean as a separate input after that product closes. |
| Noninteger complex region | `Analysis/BishopRiemannComplexAboveTwoBaselExact.agda`; `Analysis/BishopDirichletUniformBaselTailsExact.agda` | Native all-index Basel domination/region compiler exists **conditional** on source exp/log inverse and the product-derived phase bound. |
| Actual completed zeta | `Analysis/BishopMachinZetaRegularHalfPlaneExact.agda`, `Analysis/BishopMachinZetaSequentialContinuityReducerExact.agda`, `Analysis/BishopMachinQuantitativeZetaCommutingSquareExact.agda` | Original evaluation square and epsilon/delta-to-sequential-limit reducer exist. **OPEN:** finite-term continuity, sum continuity and equality to the actually selected `ZetaHalfPlaneLayer.zetaHalfPlane` and completed zeta, not merely a free record witness. |
| Machin rational / quarter | `Foundations/BishopMachinRationalTangentAlgebraExact.agda`, `Foundations/BishopMachinQuarterAngleBranchExact.agda`, `Analysis/BishopMachinQuarterPhaseQuadruplicationAlgebraExact.agda` | Rational identity, bracket and fourfold polynomial reuse written. **OPEN:** original Bishop arctan/tangent semantic quarter equality and independent trigonometric/geometric pi uniqueness. |
| NEW: actual Round11 2 pi_M period | `Analysis/BishopMachinTwoPiPeriodFromImaginaryProductExact.agda` | `round11SineTwoPiPeriod`, `round11CosineTwoPiPeriod`, `round11TwoPiPeriodPair`: source-written, no new axioms, **conditional** on ONE mixed Cauchy law and quarter `cos_B(theta_M) ≃ sin_B(theta_M)`. Not least-positive-period uniqueness. |

## Exact remaining maximal cut, in proof order

**K05-PRODUCT (P0)** — Prove `Round11ImaginaryExpMultiplicative inputs` for the original `Route.round11MachinTranscendentals inputs` and all Bishop reals x,y. Compile it from mixed signed factorial coefficients on `Real` with the existing finite convolution/reindexing and absolute-convergence/wing limits. The real-only `bishopExpAdd`, source-backed DLMF trigonometry, and abstract `ConstructedRealExponential` are not same-object substitutes. Output Pythagorean, both additions, phase modulus, π-shift and newly compiled 2π periodicity **from this single theorem**.

**K04d-LOG (P0)** — For every n ≥ 1, prove `Exp.bishopExp (Terms.sourceCanonicalNatLogCandidate n) ≃ NatReal.natReal (suc n)`. The n=0 case is already proved. A possible source-native route is the identity exp_B(Σ_{k≥1}x^k/k) ≃ (1-x)^(-1) for 0<x<1, instantiated at the rational `Terms.natLogArgument`, with actual series-composition convergence and reciprocal uniqueness. Do not assert it from the generic logarithm-inverse record; its carrier and series identification must be proved.

**K04d-REGION (automatic downstream once P0s are paid)** — Feed the native inverse and original complex Pythagorean from K05-PRODUCT to `sourceRegionWideBaselCertificate`; the local `Re(s)>2` regional tail compiler and full n=0 head are already source-written. If a broader `Re(s)>1` theorem is desired, establish a separate honest local `p`-series majorant, not the current Basel bound.

**K04d-CONTINUITY (P1, independent of the two P0s)** — Prove actual finite-term continuity of `exp_C(-sL_n)` at the selected Bishop carrier; prove uniform-limit continuity from the common Basel cutoffs and source Bishop topology; construct the selected `ZetaHalfPlaneLayer` instance or a same-object equivalence with its actual term series and the original completed-zeta evaluation. An arbitrary `ZetaHalfPlaneLayer` field alone cannot establish that equality.

**K05-PI (P1)** — Prove `cos_B(theta_M) ≃ sin_B(theta_M)` by the actual Bishop arctangent/tangent correspondence and rational Machin data; use K05-PRODUCT and quadruplication to obtain sin_B(pi_M) ≃ 0, cos_B(pi_M) ≃ -1, x↦x+pi_M antiperiod, and x↦x+2pi_M period. Then separately prove least positive period / first positive zero / quarter-angle branch uniqueness to identify this constructed pi_M with the independently selected trigonometric pi. Merely being a period does not prove uniqueness.

## Gate discipline and validation

1. Keep `{-# OPTIONS --safe #-}`, no postulates/metas/termination bypasses in every new golden proof module. Imported legacy files may contain postulates; that does not make a downstream theorem source-independent.
2. For every claimed closure record **full theorem type, source path, commit SHA, dependencies**, and the exact Agda command/run exit status. No Agda toolchain was present in this pass, so source claims remain *kernel-pending*.
3. Retain original credits: Riemann (1859), Dirichlet, Cauchy, Machin (1706), Bishop & Bridges (1985), Murray (2022), Viktor Csimma's pinned bishop, prior DASHI proof owners; cite external Lean/Mathlib proof owners separately.
4. This tranche does **not** claim the Riemann hypothesis, twin-prime infinitude, or any independent Clay theorem.

**Additional K05 source corollaries:** `round11SineAtTwoPi` and `round11CosineAtTwoPi` identify the original same-series values at `2 * bishopMachinPi` as zero and one, respectively. They reuse the origin values and newly derived period. Both remain conditional on the exact same two upstream K05 inputs; no independent π uniqueness has been supplied.


## Independent Lean companion discoveries (verified repository sources)

The `dashi_lean4` companion contains a more specific result than the phrase “trig pi still entirely absent” suggests:

- `Integration/BishopVendoredMachinPiSemantics.lean` proves `eval_machinPi_eq_real_pi` for its source-faithful Bishop Machin arctangent-series mirror, by transporting actual series limits through the vendored Bishop evaluator and applying the Mathlib Machin identity.
- `Integration/BishopVendoredTrigSemantics.lean` proves `eval_sin_eq_real_sin` and `eval_cos_eq_real_cos` for source-faithful Bishop series limits.
- `Integration/BishopVendoredExponentialSemantics.lean` proves `eval_exp_eq_real_exp` for its source-faithful exponential mirror.
- `Integration/BishopRound11MachinCanonicalBinding.lean` constructs a canonical Lean Bishop binding via classical functions encoded into the Bishop completion and proves every binding with the convergence receipts equivalent in the Bishop setoid.
- Lean PR [#24](https://github.com/chboishabba/dashi_lean4/pull/24) is **provenance/kernel replay tooling**; its own description explicitly says it is not an Agda-to-Lean proof-term translator.

**Consequences:** the classical Machin semantic direction is *source-written in Lean*, not an unknown mathematical construction. Agda can reuse its exact statement and attribution when planning the terminal weld, but cannot silently use a Lean proof term as an Agda proof term. The remaining golden acceptance criterion is native Agda theorem/proof object (or a genuinely verified proof-term import) connecting the exact original Round11 term limits to that same semantics, plus any independently specified positive-least-period characterization. This distinction prevents re-solving classical Machin arithmetic while preserving the user's Agda-first standard.


## 2026-11-03 continuation — original four gates, new proof subcuts

GitHub Agda PR [#1408](https://github.com/chboishabba/dashi_agda/pull/1408) is the **golden** lane. Lean companion is new **draft** [#104](https://github.com/chboishabba/dashi_lean4/pull/104), branched from `main` (do NOT count the older merged/closed Lean PR #24 as the live review). No exact-head Agda or Lean kernel check is observed for the new work. Source readback is not elaboration.

### K04d-LOG — actual native exponential inverse

New golden file `DASHI/Foundations/BishopNegativeLogExponentialReciprocalFromCancellationExact.agda` proves the source-level lemma:

- for the **actual convergent original** `sourceNegativeLogValue x` and `0<x<1`, `exp_B(-L(x)) ≃ 1-x` implies `exp_B(L(x)) ≃ BishopInverse(1-x)`;
- `negativeLogExpAndMinusExpCancel` is unconditional from the preexisting exact Bishop all-real Cauchy theorem;
- `negativeLogExpCancelsOneMinus` and `negativeLogExpIsActualBishopInverse` are fully proof-written reducers. The *newly isolated mathematical gate* is **the native negative exponential geometric identity** `exp_B(-L(x)) ≃ 1-x`. Its own coefficient convergence/analytic proof is still OPEN.

Companion Lean file `Integration/BishopNegativeLogNativeRound11Semantics.lean` source-mirrors precisely `x^(n+1)/(n+1)`, faithful Bishop resampled finite sums, and actual Bishop convergence, then uses Mathlib's `Real.hasSum_pow_div_log_of_abs_lt_one` and the evaluator's setoid reflection to derive `originalNatLog_successor_exp_inverse` in the source-faithful **Lean** Bishop completion when its *existing Agda* original series convergence is bound. This is a conditional **cross-prover** path, not an Agda kernel proof-term import.

### K05-PRODUCT — same original sine/cosine

Lean `Integration/BishopRound11ImaginaryProductSemanticReflection.lean` source-writes `sourceSineAddition`, `sourceCosineAddition`, and `sourceImaginaryExponentialProduct` for every `Round11MachinSourceBinding`. It evaluates the *original* signed-factorial Bishop limits, applies independently proved classical trig equations, and reflects equality into the vendored Bishop setoid. This is a real mathematical **Lean semantic proof** on source-faithful functions. It is **not** a direct native Agda mixed signed-factorial finite Cauchy coefficient proof. That exact native coefficient theorem and limit transport remain OPEN. Existing `BishopRound11ImaginaryProductPythagoreanReuseExact` already compiles the required Agda Pythagorean and modulus as consumers once product is paid.

### K04d-CONTINUITY — selected zeta must be the same function

Lean `Integration/BishopRiemannZetaNativeMachinContinuity.lean` source-writes:
- finite `originalDirichletTerm_continuous` for `exp(-s log(n+1))`;
- `originalDirichletTerm_eq_cpow` and genuine `originalDirichletValue_eq_riemannZeta` for `Re(s)>1`, using Mathlib's independently proved exact classical sum;
- `riemannZeta_continuousAtMachinPi` and `completedRiemannZeta_continuousAtMachinPi` on the **selected original Mathlib zeta** at the source-faithfully evaluated Bishop Machin pi.

This is not equality with an arbitrary instance of Agda `RiemannAnalyticSubstrate.ZetaHalfPlaneLayer`. The golden Agda obligations remain: actual local finite-term continuity, common-Basel to-limit continuity on original Bishop complex, concrete selected half-plane zeta function construction/identification, and the completed function's same-object bridge. A selected arbitrary `Function` record is not enough.

### K05-PI — first sine zero and source quarter equality

New golden `DASHI/Analysis/BishopMachinFirstPositiveSineZeroFromNativePhaseExact.agda`:
- `sourceMachinPiStrictPositive` reuses the actual rational Machin lower window;
- `sourceMachinFirstSineZeroFromNativePhase` packages `sin_B(pi_M)≃0` via the **same** original imaginary product and quarter `cos_B(theta_M)≃sin_B(theta_M)`;
- `nativeSineNoPriorZero` rules out *any earlier positive zero*, given only `NativeSinePositiveBeforeMachinPi` on the actual series. This avoids a logically invalid classical trichotomy on Bishop reals. The sign theorem is still OPEN.

Lean `sourceMachinQuarterCosineEqualsSine`, `sourceMachinPiEvaluatesToClassicalPi`, and `sourceMachinPi_is_first_positive_sine_zero` prove the mirror's full classical first-positive-zero semantics, via the existing source-faithful completion and independent Mathlib trig inequalities. Again, no unobserved proof-term transfer to golden Agda and no assertion of least-positive-**period** uniqueness.

### Updated minimal dependency cut and completion test

- **P0-L:** native source analytic identity `exp_B(-L(x)) ≃ 1-x` on the original Bishop negative-log sum, plus direct rational Nat substitution/reciprocal cancellation.
- **P0-T:** native mixed signed-factorial finite Cauchy coefficients and convergence through the original `BishopSetoidComplexExact.expC` on the selected Round11 dataset.
- **P1-Z:** native selected Bishop finite-term continuity and its uniform-limit theorem, plus *actual* `ZetaHalfPlaneLayer.zetaHalfPlane` / `CompletedRiemannZeta.zeta` same-object identification.
- **P1-π:** native source atan/tangent quarter equality and `NativeSinePositiveBeforeMachinPi` (or a correctly imported source-faithful semantic proof) for first-positive-zero minimality. A distinct period-uniqueness statement requires its own theorem.

All new Agda golden files begin with `{-# OPTIONS --safe #-}`, contain no literal `postulate`, meta hole or termination bypass in the source. Their **transitive imports and exact-head elaboration have not been kernel-verified**, so acceptance remains OPEN. All Lean claims likewise remain source-written until their focused `lake env lean` checks run and pass on exact head. Lean PR #104 adds commands to its focused workflow and axiom printout. Preserve original mathematical and implementation author attribution.

### 2026-11-03 final source-audit detail: literal K05 quarter bridge

The Lean companion [PR #104](https://github.com/chboishabba/dashi_lean4/pull/104) now includes `originalSourceMachinAtanQuarter`, the **literal** `4 atan_B(1/5) - atan_B(1/239)` on the same pinned Bishop arctangent convergence binding. `originalAtanQuarter_equiv_MachinPiQuarter` transports this expression to the Bishop setoid class of `machinPiB/4`, and `originalAtanQuarterCosineEqualsSine` proves the quarter sin=cos at that *actual* arctangent expression in the faithful Lean mirror. This corrects the possible same-object gap of proving only a synthetic pi/4 alias. No cross-prover proof-term replay or exact-head Lean/Agda kernel acceptance is observed. In native golden Agda the original quarter equality remains OPEN.

Pinned Mathlib v4.28 source readback verified the exact series theorem `Real.hasSum_pow_div_log_of_abs_lt_one`, the actual `zeta_eq_tsum_one_div_nat_add_one_cpow`, `differentiableAt_riemannZeta`, `differentiableAt_completedZeta`, and complex `natCast_log`. This is an API source check, not a successful Lean elaboration.


## 2026-11-03 continuation round: source-log convergence and actual factorial Cauchy coefficient

This round made two **new, narrower proof improvements** on Lean draft [#104](https://github.com/chboishabba/dashi_lean4/pull/104):

1. **K04d LOG Lean source-mirror now has no free log convergence package.** `Integration/BishopNegativeLogNativeRound11Semantics.lean` defines `canonicalNegativeLog = encode(-Real.log(1-eval(x)))` and proves `canonicalNegativeLog_converges` to the *literal vendored Bishop-resampled* negative-log partial sums using `bishopConvergesTo_of_eval_tendsto`, the pinned Bishop convergence/evaluation equivalence, and Mathlib's exact logarithm-series sum. `anyOriginalNegativeLogLimit_equiv_canonical` identifies ANY original limit of the very same coefficients; `anyOriginalNatSuccessorExpInverse` concludes exp-inverse for arbitrary genuine source `Sequence.lim` representatives carrying their original convergence theorem. No free `NativeNegativeLogSourceConvergence` field is needed for the canonical construction. **Still not an Agda kernel theorem.**
2. **K05 PRODUCT Lean finite coefficients are now source-written, not solely semantic trigonometry.** `Integration/BishopPureImaginaryFiniteCauchyCoefficientsExact.lean` proves for all n (in source code, kernel pending) the finite factorial/binomial convolution of `(i*x)^n/n!` and `(i*y)^n/n!` to `(i*(x+y))^n/n!`. It specifically uses `Nat.cast_choose` and `add_pow`, not `Complex.exp_add`, `Real.sin_add`, or prior Pythagorean. The formal Agda missing splice is termwise parity/source `BishopPowerSeriesElementaryBridgeExact.sineTerm/cosineTerm` identification and absolute-Cauchy-product convergence on the exact Bishop carrier; *real-only* `BishopExponentialFiniteCauchyCoefficientExact` is not that mixed complex product.
3. **Independent executable exact regression observed:** `scripts/check_bishop_imaginary_factorial_cauchy.py` returned `PASS` for 33,153 integer binomial-factorial equalities, 343 rational-complex mixed coefficient instances, all even/odd alternating-parity checks, and Machin rational 1/5 and 1/239; uses exact `Fraction`, no floating point. This is a bounded check, **not universal theorem or Agda/Lean kernel acceptance**. The script and focused Lean kernel/axiom checks are wired into PR #104 workflow, but no new workflow run has been observed.

**Current exact Agda frontier remains all four:** source negative-log exponential inverse; mixed signed factorial same-series `expC` product; finite-term and uniform-limit Bishop continuity with selected `ZetaHalfPlaneLayer.zetaHalfPlane` and completed same-object realization; and native quarter arctangent/tangent plus trigonometric pi independence. These must not be marked paid by successful Lean shadow or Python regression. Source typechecks and transitive safe imports have not been verified with Agda on exact head.
