module DASHI.Physics.Closure.NSTriadKNCauchyPolarizationCriticalBarrierBoundaryRound576Exact where

------------------------------------------------------------------------
-- ROUND576 / BIDI ADEQUACY: CAUCHY POLARIZATION IS VALID BUT NOT YET SHORTER
--
-- R575 proves the exact finite alternative
--
--   2 forcingFull <= forcingQuadratic + cellQuadratic.
--
-- The introspective question is not whether that inequality is true; it is
-- whether the two positive majorants descend to already-paid cutoff-uniform
-- spacetime consumers WITHOUT importing leaf-B critical control.
--
-- The nearest standard periodic Sobolev owner, R263/R251, explicitly passes
-- its pointwise nonlinear estimate to spacetime only UNDER `CriticalBarrierTo`.
-- Therefore a route from R575's forcingQuadratic through that owner must carry
-- both a same-object weld and a critical-barrier receipt.  It cannot silently
-- be used to pay the globally-first R406 leaf A independently of leaf B.
--
-- This module is a dependency boundary, not a new scheduler.  The direct signed
-- R294/R568 budget remains the least-prerequisite A1 consumer unless a stronger
-- barrier-free producer for the two positive quadratics is found in-repo.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ)

import DASHI.Physics.Closure.NSTriadKNPeriodicSobolevSpacetimeInstanceRound263Exact as R263
import DASHI.Physics.Closure.NSTriadKNStandardSpacetimeW1AndFirstHitW3Round251Exact as R251
import DASHI.Physics.Closure.NSTriadKNLiteralForcingCellCauchyPolarizationRound575Exact as R575
import DASHI.Physics.Closure.NSTriadKNLiveCommutatorOnlyLeafABoundaryRound568Exact as R568
import DASHI.Physics.Closure.NSTriadKNLiteralR406ClayTerminalCutsetRound504Exact as R504

record PolarizedPositiveSpacetimePayment576
    (Time : Set)
    (forcingQuadratic cellQuadratic : Nat → Time → ℚ) : Set₁ where
  field
    forcingQuadraticUniformUpper576 : Set
    cellQuadraticUniformUpper576 : Set

open PolarizedPositiveSpacetimePayment576 public

module SobolevCandidate
    (Time : Set)
    (integrateTo : (Time → ℚ) → Time → ℚ)
    (mixedMass criticalSize dissipationDensity : Nat → Time → ℚ)
    (A : R263.PeriodicSobolevSpacetimeInstance
      Time integrateTo mixedMass criticalSize dissipationDensity)
    (forcingQuadratic : Nat → Time → ℚ)
    (criticalCeiling : Time → ℚ) where

  spacetime = R263.monotoneSpacetime A

  record LiteralForcingQuadraticSobolevWeld576 : Set₁ where
    field
      sameObservable576 :
        (N : Nat) (time : Time) →
        forcingQuadratic N time ≡ mixedMass N time

      criticalBarrier576 :
        (N : Nat) (terminal : Time) →
        R251.CriticalBarrierTo spacetime N terminal (criticalCeiling terminal)

  open LiteralForcingQuadraticSobolevWeld576 public

------------------------------------------------------------------------
-- Fail-closed dependency facts.
------------------------------------------------------------------------

round576R575PolarizationMathematicallyValid : Bool
round576R575PolarizationMathematicallyValid =
  R575.round575ForcingFullUpperByTwoPositiveQuadratics

round576NearestPeriodicSobolevSpacetimeProducerRequiresCriticalBarrier : Bool
round576NearestPeriodicSobolevSpacetimeProducerRequiresCriticalBarrier = true

round576SobolevProducerSameObjectWeldAutomatic : Bool
round576SobolevProducerSameObjectWeldAutomatic = false

round576PositiveCellQuadraticUniformBoundAlreadyOwnedByR446PSD : Bool
round576PositiveCellQuadraticUniformBoundAlreadyOwnedByR446PSD = false

round576PolarizationPreservesR294SignedCancellationAsConsumer : Bool
round576PolarizationPreservesR294SignedCancellationAsConsumer = false

round576PolarizationRouteDeclaredMandatory : Bool
round576PolarizationRouteDeclaredMandatory = false

round576DirectSignedR568StillLeastPrerequisiteConsumer : Bool
round576DirectSignedR568StillLeastPrerequisiteConsumer = true

round576DirectSignedBudgetClosed : Bool
round576DirectSignedBudgetClosed = R568.round568LiveCommutatorSpacetimeBudgetClosed

round576CurrentGlobalFirstResidualStillLeafA :
  R504.firstTerminalResidual R504.currentTerminalStatus
  ≡ R504.missingLiteralR406SignedCrossPayment
round576CurrentGlobalFirstResidualStillLeafA = R504.currentFirstTerminalResidual

round576ClayPromotion : Bool
round576ClayPromotion = false

round576PolarizationRouteDeclaredMandatoryIsFalse :
  round576PolarizationRouteDeclaredMandatory ≡ false
round576PolarizationRouteDeclaredMandatoryIsFalse = refl

round576ClayPromotionIsFalse : round576ClayPromotion ≡ false
round576ClayPromotionIsFalse = refl
