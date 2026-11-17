module DASHI.Analysis.BishopOriginalFiniteErrorEqualMeshComparisonExact where

------------------------------------------------------------------------
-- K04d P0.06: FINITE MESH ERROR BOUND AT THE SAME LITERAL x.
--
-- All prior finite-walk results are now instantiated on the exact
-- source clipped equal mesh with (n+1) steps x/(n+1). The endpoint
-- v_(n+1) agrees with x by original Nat reciprocal cancellation.
--
-- For 0<=x<1, ALL stage N and ALL refinement indices n:
--
-- |F_N(x)-(1-x)| <= inv(1-(x+1)/2)^2 *
--   [ x^(N+1)/(N+1) + x*B_N(x,x/(n+1)) ].
--
-- The second term converges to zero at fixed stage N by the
-- already constructed native source quotient modulus.
-- No unproved FTC, generic uniform mesh interface or new log.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Unnormalised using (0ℚᵘ)
import Real as R
import RealProperties as RP

import DASHI.Analysis.BishopOriginalClippedEqualMeshExact as Clip
import DASHI.Analysis.BishopOriginalClippedMeshDefectRemainderExact as Remainder
import DASHI.Analysis.BishopOriginalFiniteErrorQuadratureRemainderBoundExact as ErrorBound
import DASHI.Analysis.BishopOriginalFiniteNormalizedRadiusBudgetExact as Radius
import DASHI.Analysis.BishopOriginalNegativeLogFiniteWeightedMeshRecurrenceExact as Mesh
import DASHI.Analysis.BishopOriginalNegativeLogExpFiniteStageLimitExact as Finite
import DASHI.Analysis.BishopOriginalNegativeLogFiniteErrorDerivativeExact as Error
import DASHI.Analysis.BishopOriginalFiniteLogExpStagewiseUniformDefectExact as Defect
import DASHI.Foundations.BishopNegativeLogGeometricSourceConvergenceExact as Log
import DASHI.Foundations.BishopExponentialSetoidCongruenceExact as ExpCong
import DASHI.Foundations.BishopFiniteDegreeOneGeometricBoundExact as Gap
import DASHI.Foundations.BishopNatRealReciprocalSquareBaselExact as Recip

originalFiniteNegativeLogPartialCongruent :
  (stage : Nat) (x y : R.ℝ) →
  R._≃_ x y →
  R._≃_
    (Finite.originalLogFinitePartial x stage)
    (Finite.originalLogFinitePartial y stage)
originalFiniteNegativeLogPartialCongruent zero x y same =
  RP.≃-refl
originalFiniteNegativeLogPartialCongruent (suc n) x y same =
  RP.+-cong
    (originalFiniteNegativeLogPartialCongruent n x y same)
    (RP.*-cong
      (RP.pow-cong (suc n) same)
      RP.≃-refl)

originalFiniteNegativeLogExpCongruent :
  (stage : Nat) (x y : R.ℝ) →
  R._≃_ x y →
  R._≃_
    (Finite.originalNegativeLogFiniteExponential x stage)
    (Finite.originalNegativeLogFiniteExponential y stage)
originalFiniteNegativeLogExpCongruent stage x y same =
  ExpCong.bishopExpCongruent
    (RP.-‿cong
      (originalFiniteNegativeLogPartialCongruent stage x y same))

originalFiniteNegativeLogErrorCongruent :
  (stage : Nat) (x y : R.ℝ) →
  R._≃_ x y →
  R._≃_
    (Error.originalFiniteLogExpError stage x)
    (Error.originalFiniteLogExpError stage y)
originalFiniteNegativeLogErrorCongruent stage x y same =
  RP.+-cong
    (originalFiniteNegativeLogExpCongruent stage x y same)
    (RP.-‿cong
      (RP.+-cong RP.≃-refl (RP.-‿cong same)))

originalZeroPositivePower :
  (n : Nat) →
  R._≃_ (R.pow R.0ℝ (suc n)) R.0ℝ
originalZeroPositivePower n =
  let open RP.ℝ-Solver in
  solve 1
    (λ pp → pp ⊗ Κ 0ℚᵘ ⊜ Κ 0ℚᵘ)
    RP.≃-refl (R.pow R.0ℝ n)

originalClippedEndpointPowerDifferenceIsTargetPower :
  (x : R.ℝ) (meshIndex stage : Nat) →
  let
    steps = Clip.sourceClippedEqualSteps x meshIndex
  in
  R._≃_
    (R._-_
      (R.pow (Mesh.sourceVertex steps (suc meshIndex))
        (suc stage))
      (R.pow (Mesh.sourceVertex steps zero)
        (suc stage)))
    (R.pow x (suc stage))
originalClippedEndpointPowerDifferenceIsTargetPower
    x meshIndex stage =
  RP.≃-trans
    (RP.+-cong
      (RP.pow-cong (suc stage)
        (Clip.originalClippedEqualMeshEndpointIsX x meshIndex))
      (RP.-‿cong (originalZeroPositivePower stage)))
    (RP.+-identityʳ (R.pow x (suc stage)))

originalFiniteLogErrorEqualMeshComparison :
  (stage : Nat) (x : R.ℝ) →
  (ratio : Gap.BishopUnitIntervalRatio x) →
  (meshIndex : Nat) →
  let
    h = Clip.sourceEqualStep x meshIndex
    recip = R._⋆ (Recip.reciprocalNatRational stage)
    k = Radius.sourceMidpointInverseSquare x ratio
    b = Defect.sourceOriginalUniformErrorBudget stage x h
  in
  R._≤_
    (R.∣ Error.originalFiniteLogExpError stage x ∣)
    (R._*_ k
      (R._+_
        (R._*_ recip (R.pow x (suc stage)))
        (R._*_ x b)))
originalFiniteLogErrorEqualMeshComparison
    stage x ratio meshIndex =
  let
    steps = Clip.sourceClippedEqualSteps x meshIndex
    endpoint = Mesh.sourceVertex steps (suc meshIndex)
    n = meshIndex
    xNN = Gap.ratioNonnegativeWitness ratio
    endpointSame = Clip.originalClippedEqualMeshEndpointIsX x n
    finiteBound =
      ErrorBound.originalFiniteNegativeLogExpUniformEndpointRemainderBound
        stage x ratio steps
        (Clip.originalClippedEqualMeshVertexRatio x n ratio)
        (Clip.originalClippedEqualMeshVertexBelowX x n xNN)
        (Clip.originalClippedEqualMeshStepNonnegative x n xNN)
        (suc n)
    lhsEquivalent =
      RP.∣-∣-cong
        (originalFiniteNegativeLogErrorCongruent
          stage endpoint x endpointSame)
    rhsEquivalent =
      RP.*-cong RP.≃-refl
        (RP.+-cong
          (RP.*-cong RP.≃-refl
            (originalClippedEndpointPowerDifferenceIsTargetPower
              x n stage))
          (Remainder.originalEqualClippedMeshDefectRemainderEqualsBudget
            stage x x n))
  in
  RP.≤-respʳ-≃ rhsEquivalent
    (RP.≤-respˡ-≃
      (RP.≃-symm lhsEquivalent)
      finiteBound)
