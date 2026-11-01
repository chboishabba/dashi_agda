module DASHI.Foundations.DepthWheelGradedDynamics where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.SSPPrimeLane369DepthWheelCantorBridge as Wheel

------------------------------------------------------------------------
-- C3-graded dynamics using the existing depth-wheel phase carrier.
--
-- Unlike DepthWheelSystem X, whose three phase operators are endomorphisms of
-- one carrier X, this system permits the carrier itself to depend on grade.
------------------------------------------------------------------------

record GradedDepthWheelSystem : Set₁ where
  constructor gradedDepthWheelSystem
  field
    Carrier : Wheel.DepthWheelPhase → Set
    phase0Step : Carrier Wheel.phase-0 → Carrier Wheel.phase-1
    phase1Step : Carrier Wheel.phase-1 → Carrier Wheel.phase-2
    phase2Step : Carrier Wheel.phase-2 → Carrier Wheel.phase-0

open GradedDepthWheelSystem public

oneWheelAtPhase0 :
  (system : GradedDepthWheelSystem) →
  Carrier system Wheel.phase-0 →
  Carrier system Wheel.phase-0
oneWheelAtPhase0 system x =
  phase2Step system (phase1Step system (phase0Step system x))

oneWheelAtPhase1 :
  (system : GradedDepthWheelSystem) →
  Carrier system Wheel.phase-1 →
  Carrier system Wheel.phase-1
oneWheelAtPhase1 system x =
  phase0Step system (phase2Step system (phase1Step system x))

oneWheelAtPhase2 :
  (system : GradedDepthWheelSystem) →
  Carrier system Wheel.phase-2 →
  Carrier system Wheel.phase-2
oneWheelAtPhase2 system x =
  phase1Step system (phase0Step system (phase2Step system x))

------------------------------------------------------------------------
-- Existing ungraded wheels embed as the constant graded family.
------------------------------------------------------------------------

constantGradedWheel :
  ∀ {X : Set} →
  Wheel.DepthWheelSystem X →
  GradedDepthWheelSystem
constantGradedWheel {X} system =
  gradedDepthWheelSystem
    (λ phase → X)
    (Wheel.phase0Refinement system)
    (Wheel.phase1Refinement system)
    (Wheel.phase2Refinement system)

constantWheelPhase0Agrees :
  ∀ {X : Set}
    (system : Wheel.DepthWheelSystem X)
    (x : X) →
  oneWheelAtPhase0 (constantGradedWheel system) x
  ≡ Wheel.oneWheelRenormalisation system x
constantWheelPhase0Agrees system x = refl

------------------------------------------------------------------------
-- Grading does not by itself license phase erasure.  Whether an observation
-- may quotient the grade is exactly the consumer-relative dynamic-safety
-- obligation formalised in Core.DynamicalQuotientSafety.
------------------------------------------------------------------------

record GradedDepthWheelBoundary : Set where
  constructor gradedDepthWheelBoundary
  field
    existingDepthPhaseCarrierReused : Bool
    existingDepthPhaseCarrierReusedIsTrue :
      existingDepthPhaseCarrierReused ≡ true
    existingUngradedWheelEmbeds : Bool
    existingUngradedWheelEmbedsIsTrue : existingUngradedWheelEmbeds ≡ true
    gradeMayBeForgottenWithoutSafetyProof : Bool
    gradeMayBeForgottenWithoutSafetyProofIsFalse :
      gradeMayBeForgottenWithoutSafetyProof ≡ false

open GradedDepthWheelBoundary public

canonicalGradedDepthWheelBoundary : GradedDepthWheelBoundary
canonicalGradedDepthWheelBoundary =
  gradedDepthWheelBoundary
    true refl
    true refl
    false refl
