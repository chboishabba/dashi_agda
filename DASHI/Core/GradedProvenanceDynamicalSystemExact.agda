module DASHI.Core.GradedProvenanceDynamicalSystemExact where

------------------------------------------------------------------------
-- GRADED PROVENANCE DYNAMICS
--
-- This is the exact carrier suggested by the depth-wheel/PNF synthesis:
-- observable equality is permitted to quotient fine states only when the
-- observation is a congruence for the consumer-relevant dynamics.
--
-- No psychological, cryptographic, or complexity-theoretic claim is made by
-- this generic module.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (trans; sym)

import DASHI.Foundations.DepthWheelGradedDynamics as Graded
import DASHI.Physics.Closure.SSPPrimeLane369DepthWheelCantorBridge as Wheel

------------------------------------------------------------------------
-- Pack the heterogeneous C3-graded carrier into one transition state space.
------------------------------------------------------------------------

data PackedState (system : Graded.GradedDepthWheelSystem) : Set where
  at0 : Graded.Carrier system Wheel.phase-0 → PackedState system
  at1 : Graded.Carrier system Wheel.phase-1 → PackedState system
  at2 : Graded.Carrier system Wheel.phase-2 → PackedState system

step :
  (system : Graded.GradedDepthWheelSystem) →
  PackedState system → PackedState system
step system (at0 x) = at1 (Graded.phase0Step system x)
step system (at1 x) = at2 (Graded.phase1Step system x)
step system (at2 x) = at0 (Graded.phase2Step system x)

macroStep :
  (system : Graded.GradedDepthWheelSystem) →
  PackedState system → PackedState system
macroStep system x = step system (step system (step system x))

grade :
  ∀ {system} → PackedState system → Wheel.DepthWheelPhase
grade (at0 x) = Wheel.phase-0
grade (at1 x) = Wheel.phase-1
grade (at2 x) = Wheel.phase-2

macroPreservesGrade :
  ∀ {system} (x : PackedState system) →
  grade (macroStep system x) ≡ grade x
macroPreservesGrade (at0 x) = refl
macroPreservesGrade (at1 x) = refl
macroPreservesGrade (at2 x) = refl

------------------------------------------------------------------------
-- Provenance-bearing observation/reopening.
------------------------------------------------------------------------

record GradedProvenanceSystem : Set₁ where
  constructor gradedProvenanceSystem
  field
    dynamics : Graded.GradedDepthWheelSystem
    Observation Provenance Receipt : Set
    observe : PackedState dynamics → Observation
    provenance : PackedState dynamics → Provenance
    receipt : PackedState dynamics → Receipt
    reopen : Observation → Receipt → PackedState dynamics
    reopenExact :
      (x : PackedState dynamics) → reopen (observe x) (receipt x) ≡ x

open GradedProvenanceSystem public

------------------------------------------------------------------------
-- Dynamic sufficiency: the visible dynamics factor through one coarse step.
------------------------------------------------------------------------

record DynamicallySufficientObservation
    (system : GradedProvenanceSystem) : Set₁ where
  constructor dynamicallySufficientObservation
  field
    coarseStep : Observation system → Observation system
    stepFactors :
      (x : PackedState (dynamics system)) →
      observe system (step (dynamics system) x)
      ≡ coarseStep (observe system x)

open DynamicallySufficientObservation public

sameObservationGivesSameNextObservation :
  ∀ {system}
    (safe : DynamicallySufficientObservation system)
    {x y : PackedState (dynamics system)} →
  observe system x ≡ observe system y →
  observe system (step (dynamics system) x)
    ≡ observe system (step (dynamics system) y)
sameObservationGivesSameNextObservation {system} safe {x} {y} same =
  trans
    (stepFactors safe x)
    (trans
      (cong (coarseStep safe) same)
      (sym (stepFactors safe y)))
  where
    cong : ∀ {A B : Set} {u v : A} → (f : A → B) → u ≡ v → f u ≡ f v
    cong f refl = refl

------------------------------------------------------------------------
-- Constructive witness that a quotient forgot a dynamically relevant state.
------------------------------------------------------------------------

record DynamicInsufficiencyWitness
    (system : GradedProvenanceSystem) : Set₁ where
  constructor dynamicInsufficiencyWitness
  field
    left right : PackedState (dynamics system)
    sameNow : observe system left ≡ observe system right
    nextDifferent :
      observe system (step (dynamics system) left)
      ≡ observe system (step (dynamics system) right) → ⊥

open DynamicInsufficiencyWitness public

dynamicInsufficiencyContradictsSufficiency :
  ∀ {system} →
  DynamicallySufficientObservation system →
  DynamicInsufficiencyWitness system →
  ⊥
dynamicInsufficiencyContradictsSufficiency safe witness =
  nextDifferent witness
    (sameObservationGivesSameNextObservation safe (sameNow witness))

------------------------------------------------------------------------
-- High-alpha invariant from the supplied PNF/depth-wheel analysis:
-- grade erasure is not licensed merely by current observational equality.
------------------------------------------------------------------------

record GradedProvenanceBoundary : Set₁ where
  constructor gradedProvenanceBoundary
  field
    System : GradedProvenanceSystem
    phaseIsProvenanceRelevantWhenItChangesFuture :
      DynamicInsufficiencyWitness System → Set

open GradedProvenanceBoundary public
