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


## 2026-11-03 late continuation — actual summed continuity

Lean companion PR #104 has additionally source-written `originalDirichletValue_continuousAt` on all `Re(s)>1`. It proves continuity for the entire `originalDirichletValue = ∑' exp(-s log(n+1))`, not just for finite terms, by the already source-written `originalDirichletValue_eq_riemannZeta` equality on that open domain and the existing Mathlib `differentiableAt_riemannZeta` (no singularity in `Re(s)>1`). This is a stronger **ordinary classical analytic** theorem than a claim limited to a Machin point, with zero new zeta assumptions on that Mathlib target.

**Non-promotion boundary:** the Lean equality does not identify Agda's `RiemannAnalyticSubstrate.ZetaHalfPlaneLayer.zetaHalfPlane` with Mathlib `riemannZeta`; the former is an abstract `Function` component whose `ZetaEqualsDirichletSeries` is an arbitrary `Set` field, not definitionally a concrete term equality. The Agda same-object constructor and genuinely source-native Bishop finite-term continuity/uniform-limit-to-continuity theorem are still **open**. The original `BishopDirichletUniformBaselTailsExact` already supplies uniform-to-limit errors conditional on region-wide actual domination, so do NOT add an invented second tail bound. No Lean/Agda kernel run was observed for this continuation.


## 2026-11-04 renewed native Machin source archaeology and proof work

The earlier K05-PI list was **incomplete as source archaeology**: it underemphasized actual in-repo Machin implementations. Re-audit at PR #1408 head explicitly inspected all of the following original theorem owners:

| Existing owner | Proved or provided | Not proved by that owner |
|---|---|---|
| `BishopMachinArctanConstructionExact` | Original alternating signed odd-factorial reciprocal-power series, convergence, literal `bishopMachinPi = 16 atan_B(1/5) - 4 atan_B(1/239)` | Original Bishop sine/cosine tangent semantics |
| `BishopMachinRationalTangentAlgebraExact` | Exact rational tangent double/subtract calculation, terminal formal tangent parameter = 1 | That the real constructed arctangents satisfy the induced sine/cosine tangent operation |
| `BishopMachinPiRationalWindowExact` + `BishopMachinPiArchimedesWindowExact` | Original constructive intervals 3 < pi_M < 22/7 and stronger Archimedean 223/71 < pi_M < 22/7 | Equality to an independently characterized trigonometric pi |
| `BishopMachinQuarterAngleBranchExact` | Original theta_M = 4 atan_B(1/5)-atan_B(1/239), `4 theta_M ≃ pi_M`, 3/4 < theta_M < 11/14 | `cos_B(theta_M) ≃ sin_B(theta_M)` |
| `BishopMachinQuarterPhaseQuadruplicationAlgebraExact` + `BishopRound11ImaginaryProductPythagoreanReuseExact` | Source ring-algebraic fourfold endpoint, conditional on one original pure-imaginary product and quarter sin/cos equality; one product implies Pythagorean and double-angle | The original mixed signed-factorial Cauchy coefficient theorem itself |
| `BalabanBishopSineTwoBallCubicLowerExact` + `BalabanBishopOuterBrillouinSineGapExact` | Original signed-series sine lower bound on the radius-two chart; on [3/4,11/7], sin_B(t) >= 87/128 | Global sine positivity on (0,pi_M) |
| `BishopRound11ClassicalTrigObjectWeldExact` + `BishopRound11FactorDerivativeInterchangeExact` | Common source/claim compilation for differentiation/Pythagorean and original finite derivative-term/reindexed convergence | A semantic source-backed weld inhabitant or derivative/limit interchange; these are explicitly still required |
| `BalabanWilsonFourierMachinPeriodCarrierExact` | Wilson Fourier period parameter is *definitionally chosen* from the original constructed Machin real | Independent proof that this chosen parameter is trigonometric least-positive period |
| `BishopMachinTwoPiPeriodFromImaginaryProductExact` | Original signed-series 2pi_M periodicity conditional on the one K05 product and theta_M quarter equality | Minimal period and unconditional first sine zero |

### New GOLDEN source theorem owner: Machin complement reflection

`DASHI/Analysis/BishopMachinPiComplementReflectionFromImaginaryProductExact.agda` uses the real selected Round11 parity and previously derived source pi_M anti-periodicity to prove **without any new assumptions beyond the existing K05 product and quarter equality**:
- `machinComplementAsNegativePlusPi`: exact Bishop ring setoid rearrangement `pi_M-x ≃ (-x)+pi_M`.
- `machinComplementInvolutive`: original Machin complement as a setoid involution.
- `round11SineMachinComplement`: `sin_B(pi_M-x) ≃ sin_B(x)` on the actual Round11 terms.
- `round11CosineMachinComplement`: `cos_B(pi_M-x) ≃ -cos_B(x)` on the same selected terms.

This removes a *separate* reflection-identity obligation from global native sine positivity once K05 PRODUCT and quarter equality are proved. It does not claim the general (0,pi_M) interval split or first-zero theorem by itself.

### New GOLDEN source theorem owner: strict quarter-angle sine positivity

`DASHI/Analysis/BishopMachinQuarterStrictSineFromTwoBallExact.agda` directly instantiates the *existing original* radius-two alternating series source theorem with the original `Round11.round11ConcreteTermIdentification`, **without assuming K05 product, Pythagorean or trig/atan equality**.

The real Machin branch gives `3/4 < theta_M < 11/14`. A direct rational comparison gives `theta_M <= 11/7` and `|theta_M| <= 2`. Hence `BalabanBishopOuterBrillouinSineGapExact.sineAboveEightySevenOverOneTwentyEight` supplies:
`87/128 <= E.bishopSin (Round11.elementarySeries inputs) theta_M`.
Positivity of the rational `87/128` then gives `round11MachinQuarterSineStrictPositive`, an **unconditional native signed-series branch result relative to the existing Round11 data**. This removes any separately assumed positive-sine branch at the actual Machin quarter.

Both new files carry `{-# OPTIONS --safe #-}` and are imported into the three TOE roots; **source-written only**. This turn has not observed an exact-head successful Agda kernel check and does not label the theorems accepted.

### Revised smallest FOUR-gate cut (not an invented set of assumptions)

- **K04d LOG:** original Bishop source negative-log exponential inverse `exp_B(-L(x)) ≃ 1-x` at Nat successors (the real exp(x)exp(-x) cancellation, original Nat log convergence and positive Nat rational geometry are already owned). Do not regard the completed Lean faithful-series mirror as an Agda proof importer.
- **K05 PRODUCT:** original native all-degree *complex* signed factorial Cauchy coefficient + actual Bishop double-series absolute-limit transport. The real-only coefficient proof and Lean shadow do not themselves discharge this. Then original Pythagorean, addition, Machin complement, period follow from existing reducers.
- **K04d CONTINUITY:** original Bishop finite-term continuity, uniform-limit construction (reuse `BishopDirichletUniformBaselTailsExact`) and genuine same-object identification with the selected `RiemannAnalyticSubstrate.ZetaHalfPlaneLayer` and `CompletedRiemannZeta`. The abstract `ZetaEqualsDirichletSeries : Complex → Set` is not the required equality unless inhabited with its actual semantics.
- **K05 PI:** first prove actual original atan/tan `cos_B(theta_M)≃sin_B(theta_M)`; the rational tangent arithmetic, theta_M window, **strict positive sine at theta_M**, and fourfold endpoint algebra are now source owners. First positive sine zero further needs positive sine on (0,pi_M); the existing radius-two cubic lower and new pi_M complement reflection may eliminate much of that proof, but the interval argument remains OPEN.

Do not conflate a Fourier period *chosen* to be pi_M with an independent proof that pi_M is the unique trigonometric pi. Preserve the historical attribution (Machin, Archimedes, Bishop/Bridges, Murray/Csimma, Balaban and the original DASHI theorem owners). No source-backed theorem is paid merely by setting a `ProofLevel` field.


### Same-source Machin half-phase compilation (2026-11-04)

New `DASHI/Analysis/BishopMachinHalfPhaseFromImaginaryProductExact.agda` eliminates an additional standalone angle/endpoint equality. The original `Quarter.fourTimesQuarterIsMachinPi`, `Quad.twiceTwiceIsFourTimesQuarter`, `Product.round11DoubleAngleFromImaginaryProduct`, `Product.round11PythagoreanFromImaginaryProduct`, `Quad.sinDoubleIsOneAtEqualUnitPhase`, and `Quad.cosDoubleIsZeroAtEqualPhase` are composed to construct:
- `doubleMachinHalfIsOriginalPi`: `2*(2theta_M) ≃ pi_M` on the **original** constructed Bishop Machin real, with no new assumptions;
- `round11MachinHalfSineIsOne`: `sin_B(2theta_M) ≃ 1` on the same Round11 series from the **already single** K05 imaginary product and original quarter equality;
- `round11MachinHalfCosineIsZero`: `cos_B(2theta_M) ≃ 0` under those same two inputs.

No separate half-phase sign/Pythagorean/double-angle authority is needed. Combined with the new unconditional `sin_B(theta_M)>0` and conditional `sin_B(pi_M-x)=sin_B(x)`, this sharpens the geometric/sign route: establish the native mixed product and actual atan→quarter equality first; obtain local positivity and a constructive interval split covering all `0<x<pi_M` from the **existing radius-two alternating sine lower** plus reflection. A complete locatedness/interval split and local strict cubic positivity beyond the existing quarter fibre are **not yet proved**; no first-positive-zero promotion is claimed.

This module is source-written with `{-# OPTIONS --safe #-}` and imported by all three TOE roots. A successful Agda kernel check has not been observed.

## 2026-11-04 — K05 first-positive-zero SIGN discharge from pinned Bishop locatedness (source-written)

**New source theorem owners** on golden PR #1408:

1. `DASHI/Analysis/BishopSinePositiveTwoBallFromCubicExact.agda`. This finally extends the existing radius-two source interlacing theorem from a nonstrict **cubic** lower bound to strict positivity of the *original* Round11 signed-factorial sine. It uses native exact setoid arithmetic:
   `|x|<=2 ⇒ x*x<=4 ⇒ 1-x*x/6 >= 1/3 >0`;
   `0<x ⇒ 0<x(1-x*x/6)=x-x^3/6<=sin_B(x)`.
   The proof consumes the actual `BalabanBishopSineTwoBallCubicLowerExact.sineCubicLowerTwoBall` and `Round11.round11ConcreteTermIdentification`. **No** imaginary product, trigonometric identity, Machin equality or differentiation is an input.

2. `DASHI/Analysis/BishopMachinPiGlobalSineSignFromTwoBallExact.agda` reuses the EXACT **pinned vendor/bishop** `RealProperties.fast-corollary-2-17`: for separated rational thresholds `3/2<2`, every Bishop x satisfies `x<2 ⊎ 3/2<x` constructively. For `0<x<pi_M`, branch 1 uses the newly proven radius-two sine positivity; branch 2 uses the actual Machin interval `pi_M<22/7` to show `0<pi_M-x<22/7-3/2=23/14<2`, then the already derived same-series `round11SineMachinComplement` to transfer strict positivity back to x. The exact rational inequalities were independently checked with Python Fraction (3/2<2, 23/14<2, 1−4/6=1/3). No excluded-middle or undecidable real trichotomy.

3. `round11MachinPiIsFirstPositiveSineZero` uses the **existing original** `BishopMachinFirstPositiveSineZeroFromNativePhaseExact.sourceMachinFirstSineZeroFromNativePhase`, but now supplies its previous free `NativeSinePositiveBeforeMachinPi` hypothesis with a source-written inhabitant instead of passing it in. Hence **K05-PI no longer has a separate global sine-sign or least-positive-zero leaf**. It is reduced to exactly two original source theorem dependencies: `Round11ImaginaryExpMultiplicative inputs` (K05-PRODUCT) and the actual quarter analytic equality `Quad.quarterCos inputs ≃ Quad.quarterSin inputs` (K05-PI). Those inputs are still UNPROVED in golden Agda, so the terminal π equality is not unconditional.

**Pinned upstream signature audit:** `viktorcsimma/bishop@240e38c7f6938f20f865b1f956c5f084da48bd54/RealProperties.agda` was fetched, confirming `fast-corollary-2-17`, `neg-mono-<`, `+-monoʳ-<`, `≤-respˡ-≃`, `<-respˡ-≃`, `<-respʳ-≃`, `*-monoˡ-≤-nonNeg`. The new source uses these original, non-postulatory operations and explicitly corrected left-setoid-order transport orientation in the earlier `BishopMachinQuarterStrictSineFromTwoBallExact` as well.

The two new golden modules are imported in all three canonical TOE roots, start with `{-# OPTIONS --safe #-}`, and contain no literal postulate, meta hole or termination bypass. **Agda kernel elaboration still has NOT been observed; source-writing is not completion.**

### Updated Pareto frontier after this source implementation

1. **P0 K05-PRODUCT:** native signed-factorial mixed complex finite Cauchy coefficient and absolute-limit law on the selected Round11 Bishop complex.
2. **P0 K05-QUARTER:** native atan/tangent same-object theorem proving `cos_B(theta_M)≃sin_B(theta_M)`, using already owned 4atan−atan rational tangent algebra, branch interval and now independent strict sine sign at quarter.
3. **P1 K04d-LOG:** original canonical negative-log inverse `exp_B(-L(x))≃1-x` with original Nat successor argument (Lean mirror is not an Agda import).
4. **P1 K04d-CONTINUITY:** actual Bishop source finite-term/compact uniform-limit continuity and concrete identification with the selected abstract half-plane and completed zeta objects.

The theorem `round11MachinPiIsFirstPositiveSineZero` is **source-written conditional on 1 and 2**; do not leave a third independent K05 interval-sign obligation in the remaining max-cut, and do not call it an unconditional π proof until these two proofs and Agda safe kernel checks are paid.


## 2026-11-04 continuation — finite Bishop-complex rectangle and original-series limit

**Golden source owner:** `DASHI/Analysis/BishopRound11NativeComplexRectangleExact.agda` (new). Reused the existing `BishopFiniteSeriesRectangleProductExact.rectangleProduct` for all four Cartesian coordinates, the actual `BishopSetoidComplexExact.BishopComplex` / `_≈C_` / `expC`, the original `BalabanBishopConcreteSineCosineTermParityExact` signed terms, and the original `Round11MachinSetoidComplexInstanceExact` convergence witnesses.

- `complexFiniteRectangleProduct`: fully source-written finite rectangle = product of finite partial sums for arbitrary histories in the **actual** Bishop setoid-complex carrier.
- `round11PhaseRectangleIsProduct`: direct original Round11 signed-factorial specialization; no synthetic or abstract complex semiring.
- `round11PhaseSeriesConvergesToOriginalExp`: two native Bishop convergence witnesses now identify the grouped signed-factorial complex phase history with the **actual** `expC(i*x)` limit.
- `complexFinitePartialProductsConverge` and `complexRectangleConvergesToProduct`: existing Bishop sequence sum, product, negation and setoid-equivalence limit laws extend the finite rectangle identity to the infinite **rectangle**.
- `round11RectangleConvergesToOriginalExpProduct`: the actual grouped Round11 rectangular sums converge coordinatewise to `expC(i*x) *C expC(i*y)`. This does not assume an imaginary exponential multiplication theorem.
- Both the new owner and its original imports are exposed from all three canonical TOE import roots. No ESD files changed.

**Remaining K05-PRODUCT max-cut is now narrower:** prove the all-degree mixed parity/factorial coefficients and the grouped signed-cosine/sine **rectangle-to-triangle** wing convergence/reindexing. The grouped index pairs even and odd Taylor degrees; one must NOT assert that their naive degree-n triangular convolution directly equals the grouped degree-n coefficients at x+y. Use the existing finite Cauchy triangle/wing owners with an explicit parity-sensitive regrouping and a common absolute majorant, then apply Bishop uniqueness of limits.

**Unchanged independent gates:** K04d-LOG original negative-log exp inverse and Nat transport; K04d-CONTINUITY finite-term/local-uniform/same-object selected zeta; K05-PI original atan-to-trig quarter equality. Downstream K05 first-positive-zero remains conditional only on K05-PRODUCT and that quarter equality. The new source is `{-# OPTIONS --safe #-}`, contains no locally declared postulate or hole, but **no observed exact-head Agda kernel acceptance**; all declarations remain proof candidates until checking. No claim about completed zeta or original Riemann's zeta is promoted from a generic function record.

**Attribution:** original finite Cauchy theorem authors and DASHI Round11/complex series authors, Cauchy, Machin, Bishop–Bridges, Zachary Murray, Viktor Csimma. Lean #104 remains a separate source-faithful companion, not an Agda proof transporter.


### 2026-11-04 exact *grouped* signed-factorial Cauchy correction

The ordinary ungrouped complex Taylor series has coefficients `a_n(x)=(i*x)^n/n!`.
The **original Round11 phase** instead groups `b_n(x)=a_(2n)(x)+a_(2n+1)(x)`
because its n-th cosine and sine terms carry even and odd factorial degrees.
A naive coefficient assertion `sum(k=0..n,b_k(x)*b_(n-k)(y))=b_n(x+y)` is **false**.
The missing odd/odd boundary matters even at the first row.

Define `O_n(x,y)=sum(k=0..n,a_(2k+1)(x)*a_(2(n-k)+1)(y))`, `O_(-1)=0`.
The mathematically correct universal finite identity to formalize is

```text
sum (k=0..n) b_k(x)*b_(n-k)(y)
  = b_n(x+y) + O_n(x,y) - O_(n-1)(x,y).
```

The correction follows by partitioning the *ungrouped* factorial binomial theorem
according to parity of the two factor degrees: even+even and odd+odd
contribute even degree, whereas odd+even and even+odd contribute odd degree.
Thus finite Cauchy **triangles telescope**:

```text
sum (n=0..N) sum (k=0..n) b_k(x)*b_(n-k)(y)
  = sum (n=0..N) b_n(x+y) + O_N(x,y).
```

The formal remaining K05 bridge is: (1) implement this all-n equality using
the existing native Bishop factorial coefficient and parity owners;
(2) show `O_N(x,y)` vanishes as N increases, from a source-native
absolute Cauchy convolution majorant; (3) transfer the original
rectangle-to-triangle wing estimate using the very same grouped histories.
The new Bishop rectangle-limit owner already supplies the target product limit.

**Executed finite regression:** `scripts/check_bishop_round11_grouped_parity_cauchy.py`
checks both displayed identities in exact Python `Fraction` Gaussian complex
arithmetic for 25 pairs of rational inputs and 20 degrees each: **PASS 500/500**,
including the original Machin `1/5` and `1/239`. This is **not** the Agda
universal equality, nor a Bishop convergence theorem. It rules out promoting
the false uncorrected grouped coefficient formula. No exact-head Agda
elaboration receipt exists; remain kernel-pending.


**Sharper analytic target for the residual odd/odd boundary.** For real Bishop
arguments x,y the absolute value of each coefficient is its usual factorial
majorant. All summands in the odd/odd convolution correspond to the *subset*
of the nonnegative binomial terms of total degree `m=2N+2` with odd left
degree. Consequently the exact mathematical target is

```text
abs(O_N(x,y))
 <= sum(k=0..N, |x|^(2k+1)*|y|^(2(N-k)+1)
                  / ((2k+1)!*(2(N-k)+1)!))
 <= (|x|+|y|)^(2N+2)/(2N+2)!.
```

As `N → infinity` this majorant tends to zero because it is a subsequence
of the terms of the original absolutely convergent Bishop exponential
series at `|x|+|y|`. To make this native Agda, reuse
`BishopExponentialFiniteCauchyCoefficientExact` and the original
factorial/binomial coefficient embedding, with the explicit odd-index
subsum and nonnegative-sum monotonicity. Then use the pinned
`Sequence` term-vanishing-from-series-convergence lemma and subsequence
transport, not an arbitrary complex tail assumption.


## 2026-11-04 second continuation — native generic Cauchy wing, four-way Round11 triangle compiler

New golden source owner: `DASHI/Analysis/BishopGenericCauchyFromAbsoluteTriangleExact.agda`:
- `absoluteTriangle` and `positiveWing` retain the *literal* Bishop signed source histories and reuse the original `BishopFiniteCauchyRowReindexExact` and `BishopFiniteCauchyWingAbsoluteBoundExact`.
- `positiveWingConvergesZero` derives the finite positive wing tail from actual convergence of the absolute triangle by the pinned `BishopConvergentDoubleTailExact` theorem, with `double n = n+n` transported by the already-proved Nat identity.
- `rectangleConvergesToProduct` derives the genuine real rectangular product limit via `BishopFiniteSeriesRectangleProductExact.rectangleProduct` and native `Sequence.xₙyₙ→x₀y₀`.
- `reverseFiniteWingBound` derives the required *triangle-minus-rectangle* order of the wing bound, not silently applying a mismatched directional inequality.
- **`cauchyTriangleConvergesToActualProduct`** consumes only (a) actual separate Bishop series convergence and (b) absolute triangle convergence, then proves convergence of the original signed Cauchy triangle to the original product with `BishopVanishingDifferenceConvergenceExact`. No separate assumed Cauchy-product theorem, no alternate carrier.

Extended existing golden owner `DASHI/Analysis/BishopRound11NativeComplexRectangleExact.agda`:
- `complexTriangle`, `complexMertensRow` and `complexTriangleIsMertens`: finite complex Cauchy triangle and genuine four-way source-native Mertens reindexing on `BishopSetoidComplexExact`.
- `FourAbsoluteTriangles` is an **explicit unresolved premise** packaging four genuinely convergent absolute real Cauchy triangles (cos/cos, sin/sin, cos/sin, sin/cos); it is NOT claimed instantiated from source absolute sine/cosine convergence.
- `complexTriangleConvergesToProduct` and `round11PhaseTriangleConvergesFromFourAbsoluteTriangles` compile those four real generic Cauchy conclusions to the literal original Round11 `expC(i*x) *C expC(i*y)` complex product, with no new complex convergence authority.

The earlier "rectangle-to-triangle transport" gate is now **generic-source-written** on both Bishop real and complex carriers; the **remaining independent K05 content** is:
1. Build `FourAbsoluteTriangles (round11PhaseTerms inputs x) (round11PhaseTerms inputs y)` from the original absolute sine/cosine convergence and the existing positive-triangle/rectangle finite sandwich (or from the grouped factorial majorant). Do not assume a generic positive-triangle limit.
2. Prove the **correct** universal parity grouped Cauchy coefficient/telescope identity `T_N(x,y) ≃ P_N(x+y)+O_(N-1)` with index convention checked carefully, on the actual Bishop setoid complex. The prior direct uncorrected coefficient identity is false.
3. Prove the odd–odd factorial boundary tends to zero on the actual Bishop real/complex history, identify the resulting `complexTriangle` limit with the original `expC(i*(x+y))`, and apply uniqueness of limits to finish `Round11ImaginaryExpMultiplicative`.
4. Obtain an **exact-head Agda kernel acceptance receipt**. No Agda executable or observed exact-head CI success is available for these additions; they are --safe source-written proof candidates only.

K04d-LOG, K04d-CONTINUITY, K05-PI remain separately OPEN. All three TOE roots import the new generic owner. No ESD owner changed. Historical source and proof attribution to Cauchy, Bishop–Bridges, Murray/Csimma and the original DASHI owners is preserved.


## 2026-11-05 continuation — four *actual* absolute triangles and vanishing odd/odd boundary

The prior block above is a dated snapshot. The following discharges its old
source-level K05 analytic premises as source-written **proof candidates**,
not as Agda-kernel accepted theorems. Golden PR #1408.

### Actual new owners and exact theorem endpoints

1. `DASHI/Analysis/BishopRound11ConcreteAbsoluteSeriesConvergenceExact.agda`
   transports the existing `Round11.elementarySeries` sine/cosine absolute
   series convergence through `round11ConcreteTermIdentification` to the
   literal signed-factorial sequences. Both real absolute limits are selected,
   not newly assumed.
2. `DASHI/Analysis/BishopSetoidSqueezeConvergenceExact.agda` proves generic
   `nativeBishopSqueeze` directly from Bishop finite order and existing
   convergence algebra. `BishopMonotoneDoubleSubsequenceLimitExact.agda`
   proves `monotoneDoubleConvergesImpliesFullConverges` by constructive
   `Sequence.con*`, using the pinned `xₙisIncreasing⇒xₙ≤limxₙ` result.
3. `DASHI/Analysis/BishopPositiveCauchyTriangleFromAbsoluteSeriesExact.agda`
   proves `positiveCauchyTriangleConverges` for any two nonnegative Bishop
   sequences with convergent original series, by the **existing**
   `R(n,n) ≤ T(2n) ≤ R(2n,2n)` source inequalities, real product limit,
   native squeeze and monotone double subsequence. This reuses every
   original Fin-sum and Bishop carrier; it does not assume a Cauchy product.
4. `DASHI/Analysis/BishopRound11NativeComplexRectangleExact.agda` now
   source-constructs `round11SourceFourAbsoluteTriangles inputs x y`,
   using the four combinations (cos/cos, cos/sin, sin/cos, sin/sin) of the
   two actual Round11 absolute sequences. Hence
   `round11OriginalComplexCauchyTriangleConverges` no longer needs a
   caller-supplied `FourAbsoluteTriangles` witness.
5. The signed sine×sine **Cauchy triangle itself converges** with its
   original source coefficients, by
   `round11SignedSineCauchyTriangleConverges`. Consequently
   `round11SignedSineCauchyCoefficientConvergesZero` follows by pinned
   `Sequence.∑xₙisConvergent⇒xₙ→0`; and thus
   `round11OddOddCorrectionConvergesZero` is also constructed. A separate
   factorial tail-bound theorem is no longer needed for this analytic leaf.
6. `DASHI/Foundations/BishopFiniteEvenOddCauchyReindexExact.agda`
   source-writes arbitrary-history `finiteEvenOddSplit`,
   `finiteOddLengthSplit`, and literal all-degree finite Cauchy even- and
   odd-parity split theorems. No numerical case check is used to infer an
   all-N identity.
7. `DASHI/Foundations/BishopRound11SignedFactorialExponentEncodingExact.agda`
   derives original recursive `evenExponent n ≡ double n`,
   `oddExponent n ≡ suc (double n)`, identifies the actual signed
   cosine/sine terms with `alternatingSign n * Exp.expTerm x (2n/2n+1)`,
   and establishes `alternatingSignAddition` using pinned Bishop
   `xⁿxᵐ≃xⁿ⁺ᵐ`. The **finite mixed signed factorial algebra connecting**
   these to the original exponential binomial/Cauchy coefficient theorem
   remains unproved.
8. `DASHI/Analysis/BishopOneStepLagConvergenceExact.agda` builds
   constructive one-step convergence transport, needed because the finite
   Cauchy partial of N terms differs by correction O_(N-1).
9. `round11ProductFromVanishingGroupedBoundary` and
   `round11ProductFromExactFiniteGroupedParity` derive the original
   complex exponential product using **only** source finite parity
   differences and already-proved convergence/uniqueness. Existing
   `C.imaginaryExponentialProductGivesAddition` then yields both
   original sine and cosine addition laws in
   `round11TrigAdditionFromExactFiniteGroupedParity`.

### **ONE remaining independent K05 finite equality pair**

On the original complex Bishop carrier, for every n,x,y and the original
selected Round11 cutset, prove the exact finite identities:

```agda
round11GroupedBoundaryReal inputs x y (suc n)
  ≃ round11OddOddCorrection inputs x y n

round11GroupedBoundaryImag inputs x y (suc n)
  ≃ R.0ℝ
```

These are precisely the **corrected grouped factorial** Cauchy identities:
`T_(n+1) - P_(n+1) ≃ O_n`. The real odd/odd correction is already
proven to converge to zero above. Finite parity reindex and source
exponent/signed factorial identifications are written, but their
universal signed 2D convolution/binomial composition is still missing.
Do **not** substitute the false naive `b_k*b_(n-k)=b_n(x+y)`
coefficient claim. Once these two exact identities are paid and accepted,
`round11ProductFromExactFiniteGroupedParity` is the terminal source
theorem. Its `C._≈C_` conclusion is reversed as needed by the existing
`C.imaginaryExponentialProductGivesAddition`.

### Verification and distinct gates

All three canonical TOE roots import the new source owners. A narrow
`.github/workflows/bishop-k04d-k05-native-proof.yml` was added to
attempt `agda --safe` 2.6.4.3 / stdlib 2.1 checks of the exact new
dependency chain and preserve a kernel diagnostic receipt. **No passing
exact-head kernel receipt was observed at source-writing time**. Treat
the `--safe` annotations and hole-free static inspection as
insufficient for acceptance.

K04d-LOG (canonical original exp(-log) inverse and Nat successor),
K04d-CONTINUITY (native finite/uniform limit plus original and completed
zeta same-object weld), and K05-PI (original Machin atan/trig quarter
equality) remain **OPEN**, not converted into mere formalization status.
No ESD file has been intentionally edited. The original Cauchy,
Newton/binomial, Bishop–Bridges, Murray/Csimma, and DASHI source
provenance is preserved.
