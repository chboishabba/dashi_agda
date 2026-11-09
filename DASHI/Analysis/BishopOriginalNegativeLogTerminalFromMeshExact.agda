module DASHI.Analysis.BishopOriginalNegativeLogTerminalFromMeshExact where

------------------------------------------------------------------------
-- K04d P0.07: ORIGINAL BISHOP FINITE LOG-EXP -> 1-x.
--
-- Consume the source-proved finite endpoint bound:
--    |F_N(x)-(1-x)| <= K(x)*x^(N+1)/(N+1), 0<=x<1.
-- The native power sequence x^(N+1) -> 0, and the native reciprocal
-- sequence 1/(N+1) -> 0; the fixed K(x) is a genuine Bishop real.
--
-- The original vanishing-difference convergence theorem proves
--    F_N(x) -> 1-x
-- on the original, not a synthetic, real/exp carrier.
--
-- Then the ALREADY-WRITTEN terminal consumer
--    originalNegativeLogTerminalFromFiniteEvaluation
-- identifies the two actual source limits. No added LOG axiom.
--
-- The original LOG gap predicate is the existing exact public API.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; suc)
import Real as R
import RealProperties as RP
import Sequence as Seq

import DASHI.Analysis.BishopOriginalFiniteNegativeLogExpEndpointBoundExact as Bound
import DASHI.Analysis.BishopOriginalFiniteNormalizedEndpointQuadratureRemainderExact as Quad
import DASHI.Analysis.BishopOriginalFiniteNormalizedRadiusBudgetExact as Radius
import DASHI.Analysis.BishopPowerFirstOrderDifferenceFactorisationExact as Power
import DASHI.Analysis.BishopVanishingDifferenceConvergenceExact as Vanish
import DASHI.Analysis.BishopOriginalNegativeLogExpFiniteStageLimitExact as Finite
import DASHI.Analysis.BishopK04dNatLogFromOriginalGapExact as NativeLog
import DASHI.Foundations.BishopFiniteDegreeOneGeometricBoundExact as Gap
import DASHI.Foundations.BishopBaselReciprocalSquareConvergenceExact as Basel
import DASHI.Foundations.BishopNatRealReciprocalSquareBaselExact as Recip

originalSourceRadiusPowerConvergesToZero :
  (x : R.ℝ) →
  (ratio : Gap.BishopUnitIntervalRatio x) →
  Seq._ConvergesTo_
    (λ n → R.pow x (suc n))
    R.0ℝ
originalSourceRadiusPowerConvergesToZero x ratio =
  let
    xNN = Gap.ratioNonnegativeWitness ratio
    absInside =
      RP.<-respˡ-≃
        (RP.≃-symm (RP.nonNegx⇒∣x∣≃x xNN))
        (Gap.ratioBelowOne ratio)
  in
  Seq.fast-xₙ⊆yₙ∧yₙ→y⇒xₙ→y
    (Seq.shift-is-subsequence (λ n → R.pow x n) 1)
    (R.0ℝ , Seq.∣r∣<1⇒rⁿ→0 absInside)

originalSourceEndpointErrorBudgetNonnegative :
  (n : Nat) (x : R.ℝ) →
  (ratio : Gap.BishopUnitIntervalRatio x) →
  R.NonNegative (Bound.sourceOriginalFiniteErrorFinalMajorant n x ratio)
originalSourceEndpointErrorBudgetNonnegative n x ratio =
  RP.nonNegx,y⇒nonNegx*y
    (Quad.sourceMidpointInverseSquareNonnegative x ratio)
    (RP.nonNegx,y⇒nonNegx*y
      (Recip.reciprocalNonnegative n)
      (Seq.nonNegx⇒nonNegxⁿ (suc n)
        (Gap.ratioNonnegativeWitness ratio)))

originalSourceEndpointErrorBudgetConvergesZero :
  (x : R.ℝ) →
  (ratio : Gap.BishopUnitIntervalRatio x) →
  Seq._ConvergesTo_
    (λ n → Bound.sourceOriginalFiniteErrorFinalMajorant n x ratio)
    R.0ℝ
originalSourceEndpointErrorBudgetConvergesZero x ratio =
  let
    common = Radius.sourceMidpointInverseSquare x ratio
    powerConverges = originalSourceRadiusPowerConvergesToZero x ratio
    reciprocalConverges = Basel.reciprocalSequenceConvergesZero
    productConverges =
      Seq.xₙ→x∧x≃y⇒xₙ→y
        (Seq.xₙyₙ→x₀y₀
          (R.0ℝ , reciprocalConverges)
          (R.0ℝ , powerConverges))
        (let open RP.ℝ-Solver in
         solve 0
           (Κ 0ℚᵘ ⊗ Κ 0ℚᵘ ⊜ Κ 0ℚᵘ)
           RP.≃-refl)
    scaledConverges =
      Seq.xₙ→x∧x≃y⇒xₙ→y
        (Seq.xₙyₙ→x₀y₀
          (common , Power.constantConverges common)
          (R.0ℝ , productConverges))
        (let open RP.ℝ-Solver in
         solve 1
           (λ kk → kk ⊗ Κ 0ℚᵘ ⊜ Κ 0ℚᵘ)
           RP.≃-refl common)
  in
  scaledConverges

originalNegativeLogFiniteEvaluationConvergesToOneMinus :
  (x : R.ℝ) →
  (ratio : Gap.BishopUnitIntervalRatio x) →
  Seq._ConvergesTo_
    (Finite.originalNegativeLogFiniteExponential x)
    (R._-_ R.1ℝ x)
originalNegativeLogFiniteEvaluationConvergesToOneMinus x ratio =
  Vanish.vanishingDifferenceConvergence
    (Power.constantConverges (R._-_ R.1ℝ x))
    (originalSourceEndpointErrorBudgetConvergesZero x ratio)
    (λ n →
      RP.≤-respʳ-≃
        (RP.≃-symm
          (RP.nonNegx⇒∣x∣≃x
            (originalSourceEndpointErrorBudgetNonnegative n x ratio)))
        (Bound.originalFiniteNegativeLogExpUniformEndpointBound
          n x ratio))

-- Actual inhabitant of the ORIGINAL, already public terminal gap:
-- no selected LOG, no additional completeness or calculus axiom.
originalBishopNegativeLogExponentialGap :
  NativeLog.OriginalBishopNegativeLogExponentialGap
originalBishopNegativeLogExponentialGap x positive belowOne =
  Finite.originalNegativeLogTerminalFromFiniteEvaluation
    x positive belowOne
    (originalNegativeLogFiniteEvaluationConvergesToOneMinus
      x record
        { ratioNonnegative = RP.<⇒≤ positive
        ; ratioBelowOne = belowOne
        })
