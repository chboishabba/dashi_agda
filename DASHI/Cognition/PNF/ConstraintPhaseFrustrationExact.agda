module DASHI.Cognition.PNF.ConstraintPhaseFrustrationExact where

------------------------------------------------------------------------
-- CONSTRAINT FRUSTRATION, NOT RAW PHASE MISMATCH
--
-- This refines CoupledDepthPhaseFrustrationExact.  A phase difference is not
-- itself a defect: each edge declares which relative phase relation is
-- admissible.  The old disagreement cost is recovered only as one special
-- potential ("same phase required").
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.CoupledDepthPhaseFrustrationExact as Raw
import DASHI.Physics.Closure.SSPPrimeLane369DepthWheelCantorBridge as Wheel

data PhaseConstraint : Set where
  samePhase : PhaseConstraint
  nextPhase : PhaseConstraint
  unconstrained : PhaseConstraint

phaseEq :
  Wheel.DepthWheelPhase → Wheel.DepthWheelPhase → Bool
phaseEq Wheel.phase-0 Wheel.phase-0 = true
phaseEq Wheel.phase-0 Wheel.phase-1 = false
phaseEq Wheel.phase-0 Wheel.phase-2 = false
phaseEq Wheel.phase-1 Wheel.phase-0 = false
phaseEq Wheel.phase-1 Wheel.phase-1 = true
phaseEq Wheel.phase-1 Wheel.phase-2 = false
phaseEq Wheel.phase-2 Wheel.phase-0 = false
phaseEq Wheel.phase-2 Wheel.phase-1 = false
phaseEq Wheel.phase-2 Wheel.phase-2 = true

satisfies :
  PhaseConstraint →
  Wheel.DepthWheelPhase →
  Wheel.DepthWheelPhase →
  Bool
satisfies samePhase left right = phaseEq left right
satisfies nextPhase left right =
  phaseEq (Wheel.nextDepthWheelPhase left) right
satisfies unconstrained left right = true

violationCost :
  PhaseConstraint →
  Wheel.DepthWheelPhase →
  Wheel.DepthWheelPhase →
  Nat
violationCost constraint left right with satisfies constraint left right
... | true = zero
... | false = suc zero

rawMismatchCanStillBeAdmissible :
  Raw.phaseDisagreement Wheel.phase-0 Wheel.phase-1 ≡ 1
rawMismatchCanStillBeAdmissible = refl

asynchronousNextPhaseHasZeroConstraintCost :
  violationCost nextPhase Wheel.phase-0 Wheel.phase-1 ≡ 0
asynchronousNextPhaseHasZeroConstraintCost = refl

samePhasePotentialRecoversRawAt01 :
  violationCost samePhase Wheel.phase-0 Wheel.phase-1
  ≡ Raw.phaseDisagreement Wheel.phase-0 Wheel.phase-1
samePhasePotentialRecoversRawAt01 = refl

sameAndNextCannotBothHold :
  (left right : Wheel.DepthWheelPhase) →
  satisfies samePhase left right ≡ true →
  satisfies nextPhase left right ≡ true →
  ⊥
sameAndNextCannotBothHold Wheel.phase-0 Wheel.phase-0 refl ()
sameAndNextCannotBothHold Wheel.phase-0 Wheel.phase-1 () next
sameAndNextCannotBothHold Wheel.phase-0 Wheel.phase-2 () next
sameAndNextCannotBothHold Wheel.phase-1 Wheel.phase-0 () next
sameAndNextCannotBothHold Wheel.phase-1 Wheel.phase-1 refl ()
sameAndNextCannotBothHold Wheel.phase-1 Wheel.phase-2 () next
sameAndNextCannotBothHold Wheel.phase-2 Wheel.phase-0 () next
sameAndNextCannotBothHold Wheel.phase-2 Wheel.phase-1 () next
sameAndNextCannotBothHold Wheel.phase-2 Wheel.phase-2 refl ()

record ConstraintFrustrationWitness : Set where
  constructor constraintFrustrationWitness
  field
    left right : Wheel.DepthWheelPhase
    first second : PhaseConstraint
    firstSatisfied : satisfies first left right ≡ true
    secondSatisfiedWouldContradict :
      satisfies second left right ≡ true → ⊥

open ConstraintFrustrationWitness public

phaseZeroSameVsNextConflict : ConstraintFrustrationWitness
phaseZeroSameVsNextConflict =
  constraintFrustrationWitness
    Wheel.phase-0
    Wheel.phase-0
    samePhase
    nextPhase
    refl
    (sameAndNextCannotBothHold Wheel.phase-0 Wheel.phase-0 refl)
