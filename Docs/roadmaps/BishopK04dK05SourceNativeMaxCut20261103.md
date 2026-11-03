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
