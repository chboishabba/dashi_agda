module DASHI.Analysis.BishopOriginalFiniteNegativeLogExpEndpointBoundExact where

------------------------------------------------------------------------
-- K04d P0.06: ACTUAL ORIGINAL FINITE LOG EXP ENDPOINT UPPER BOUND.
--
-- At every 0<=x<1 and every source stage N, the original Bishop
-- finite exponential F_N(x)=exp_B(-L_N(x)) satisfies
--
-- |F_N(x)-(1-x)| <= K(x) * x^(N+1)/(N+1),
-- K(x)=inv_B(1-(x+1)/2)^2.
--
-- The factor K(x) is deliberately 4/(1-x)^2, not the sharper
-- 1/(1-r)^2 from the earlier goal: the midpoint radius handles
-- proof-relevant strict reciprocal order without endpoint cases.
-- It is independent of N, and sufficient for the terminal LOG.
--
-- Proof: source clipped equal mesh, exact original endpoint,
-- exact finite power quadrature, the actual quotient-defect
-- remainder, then Bishop Sequence order preservation as the
-- mesh index tends to infinity. No FTC, MVT or new exponent.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; suc)
import Real as R
import RealProperties as RP
import Sequence as Seq

import DASHI.Analysis.BishopOriginalFiniteErrorEqualMeshComparisonExact as MeshBound
import DASHI.Analysis.BishopOriginalClippedMeshDefectRemainderExact as Remainder
import DASHI.Analysis.BishopOriginalClippedEqualMeshExact as Clip
import DASHI.Analysis.BishopOriginalFiniteNormalizedRadiusBudgetExact as Radius
import DASHI.Analysis.BishopOriginalFiniteLogExpStagewiseUniformDefectExact as Defect
import DASHI.Analysis.BishopPowerFirstOrderDifferenceFactorisationExact as Power
import DASHI.Analysis.BishopOriginalNegativeLogFiniteErrorDerivativeExact as Error
import DASHI.Foundations.BishopFiniteDegreeOneGeometricBoundExact as Gap
import DASHI.Foundations.BishopNatRealReciprocalSquareBaselExact as Recip

sourceFiniteEndpointPowerBudget :
  (stage : Nat) (x : R.ℝ) → R.ℝ
sourceFiniteEndpointPowerBudget stage x =
  R._*_
    (R._⋆ (Recip.reciprocalNatRational stage))
    (R.pow x (suc stage))

sourceOriginalFiniteErrorFinalMajorant :
  (stage : Nat) (x : R.ℝ) →
  Gap.BishopUnitIntervalRatio x →
  R.ℝ
sourceOriginalFiniteErrorFinalMajorant stage x ratio =
  R._*_
    (Radius.sourceMidpointInverseSquare x ratio)
    (sourceFiniteEndpointPowerBudget stage x)

sourceOriginalFiniteMeshMajorant :
  (stage : Nat) (x : R.ℝ) →
  (ratio : Gap.BishopUnitIntervalRatio x) →
  Nat → R.ℝ
sourceOriginalFiniteMeshMajorant stage x ratio meshIndex =
  R._*_
    (Radius.sourceMidpointInverseSquare x ratio)
    (R._+_
      (sourceFiniteEndpointPowerBudget stage x)
      (R._*_ x
        (Defect.sourceOriginalUniformErrorBudget
          stage x (Clip.sourceEqualStep x meshIndex))))

sourceOriginalFiniteMeshMajorantConverges :
  (stage : Nat) (x : R.ℝ) →
  (ratio : Gap.BishopUnitIntervalRatio x) →
  Seq._ConvergesTo_
    (sourceOriginalFiniteMeshMajorant stage x ratio)
    (sourceOriginalFiniteErrorFinalMajorant stage x ratio)
sourceOriginalFiniteMeshMajorantConverges stage x ratio =
  let
    k = Radius.sourceMidpointInverseSquare x ratio
    a = sourceFiniteEndpointPowerBudget stage x
    remainderConverges =
      Remainder.originalEqualClippedMeshDefectBudgetConvergesZero
        stage x x
    plusConverges :
      Seq._ConvergesTo_
        (λ meshIndex →
          R._+_ a
            (R._*_ x
              (Defect.sourceOriginalUniformErrorBudget
                stage x (Clip.sourceEqualStep x meshIndex))))
        (R._+_ a R.0ℝ)
    plusConverges =
      Seq.xₙ+yₙ→x₀+y₀
        (a , Power.constantConverges a)
        (R.0ℝ , remainderConverges)
    productConverges =
      Seq.xₙyₙ→x₀y₀
        (k , Power.constantConverges k)
        (R._+_ a R.0ℝ , plusConverges)
  in
  Seq.xₙ→x∧x≃y⇒xₙ→y
    productConverges
    (RP.*-cong RP.≃-refl (RP.+-identityʳ a))

originalFiniteNegativeLogExpUniformEndpointBound :
  (stage : Nat) (x : R.ℝ) →
  (ratio : Gap.BishopUnitIntervalRatio x) →
  R._≤_
    (R.∣ Error.originalFiniteLogExpError stage x ∣)
    (sourceOriginalFiniteErrorFinalMajorant stage x ratio)
originalFiniteNegativeLogExpUniformEndpointBound stage x ratio =
  Seq.xₙ≤yₙ⇒limxₙ≤limyₙ
    (MeshBound.originalFiniteLogErrorEqualMeshComparison
      stage x ratio)
    (R.∣ Error.originalFiniteLogExpError stage x ∣ ,
      Power.constantConverges
        (R.∣ Error.originalFiniteLogExpError stage x ∣))
    (sourceOriginalFiniteErrorFinalMajorant stage x ratio ,
      sourceOriginalFiniteMeshMajorantConverges stage x ratio)
