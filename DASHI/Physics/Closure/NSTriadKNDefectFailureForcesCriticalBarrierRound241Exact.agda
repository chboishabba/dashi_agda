module DASHI.Physics.Closure.NSTriadKNDefectFailureForcesCriticalBarrierRound241Exact where

------------------------------------------------------------------------
-- ROUND241 / DEFECT FAILURE FORCES CRITICAL-BARRIER FAILURE
--
-- For the authoritative mixed-helicity defect, standard critical Sobolev
-- interpolation has the schematic form
--
--   Q_+-(t) <= C * A(t) * D(t),
--
-- where
--
--   A(t) = ||u(t)||_{H^(1/2)}^2,
--   D(t) = ||u(t)||_{H^1}^2.
--
-- The Galerkin energy inequality gives a cutoff-uniform integrated
-- dissipation bound
--
--   integral D_N <= D_*.
--
-- Therefore any uniform critical barrier A_N(t) <= K implies
--
--   integral Q_+-(u_N) <= C * K * D_*
--
-- uniformly in cutoff.
--
-- CONTRAPOSITIVE RESEARCH CONSEQUENCE:
-- failure of the cutoff-uniform Q_+- spacetime budget forces failure of every
-- finite uniform H^(1/2) barrier.  Hence one may select first hitting times of
-- a fixed critical threshold K and obtain a bounded critical sequence without
-- assuming Package A.
--
-- This module theoremises only the ordered scalar compiler.  The physical
-- interpolation theorem, integrated Galerkin dissipation law, and continuity
-- needed to select first hitting times remain independently owned analytic
-- receipts.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using
  (ℚ; 0ℚ; _*_; _≤_; NonNegative; nonNegative)
import Data.Rational.Properties as ℚP

record CriticalBarrierDefectPayment : Set where
  constructor critical-barrier-defect-payment
  field
    defectIntegral : ℚ
    interpolationConstant : ℚ
    criticalBarrier : ℚ
    dissipationIntegral : ℚ
    dissipationBound : ℚ

    scaledBarrierNN :
      0ℚ ≤ interpolationConstant * criticalBarrier

    defectReducedToBarrierTimesDissipation :
      defectIntegral
      ≤ interpolationConstant * criticalBarrier * dissipationIntegral

    dissipationUniformlyBounded :
      dissipationIntegral ≤ dissipationBound

open CriticalBarrierDefectPayment public

boundedCriticalBarrierPaysDefect :
  (P : CriticalBarrierDefectPayment) →
  defectIntegral P
  ≤ interpolationConstant P * criticalBarrier P * dissipationBound P
boundedCriticalBarrierPaysDefect P =
  let
    scale = interpolationConstant P * criticalBarrier P

    instance scaleNNI : NonNegative scale
    scaleNNI = nonNegative (scaledBarrierNN P)
  in
  ℚP.≤-trans
    (defectReducedToBarrierTimesDissipation P)
    (ℚP.*-monoˡ-≤-nonNeg scale (dissipationUniformlyBounded P))

round241ScalarBarrierToDefectCompilerClosed : Bool
round241ScalarBarrierToDefectCompilerClosed = true

round241PhysicalCriticalInterpolationInstalled : Bool
round241PhysicalCriticalInterpolationInstalled = false

round241PhysicalIntegratedGalerkinDissipationInstalled : Bool
round241PhysicalIntegratedGalerkinDissipationInstalled = false

round241UniformDefectFailureForcesCriticalBarrierFailure : Bool
round241UniformDefectFailureForcesCriticalBarrierFailure = true

round241FirstHitCriticalSequenceExtracted : Bool
round241FirstHitCriticalSequenceExtracted = false

round241PackageAClosed : Bool
round241PackageAClosed = false

round241ClayPromotion : Bool
round241ClayPromotion = false

round241ScalarBarrierToDefectCompilerClosedIsTrue :
  round241ScalarBarrierToDefectCompilerClosed ≡ true
round241ScalarBarrierToDefectCompilerClosedIsTrue = refl

round241PhysicalCriticalInterpolationInstalledIsFalse :
  round241PhysicalCriticalInterpolationInstalled ≡ false
round241PhysicalCriticalInterpolationInstalledIsFalse = refl

round241PhysicalIntegratedGalerkinDissipationInstalledIsFalse :
  round241PhysicalIntegratedGalerkinDissipationInstalled ≡ false
round241PhysicalIntegratedGalerkinDissipationInstalledIsFalse = refl

round241UniformDefectFailureForcesCriticalBarrierFailureIsTrue :
  round241UniformDefectFailureForcesCriticalBarrierFailure ≡ true
round241UniformDefectFailureForcesCriticalBarrierFailureIsTrue = refl

round241FirstHitCriticalSequenceExtractedIsFalse :
  round241FirstHitCriticalSequenceExtracted ≡ false
round241FirstHitCriticalSequenceExtractedIsFalse = refl

round241PackageAClosedIsFalse : round241PackageAClosed ≡ false
round241PackageAClosedIsFalse = refl

round241ClayPromotionIsFalse : round241ClayPromotion ≡ false
round241ClayPromotionIsFalse = refl
