module DASHI.Core.HiddenPhaseDynamicInsufficiencyExact where

------------------------------------------------------------------------
-- CONCRETE DYNAMIC-SUFFICIENCY COUNTEREXAMPLE
--
-- Two states expose the same current Boolean content, but occupy different C3
-- phases.  Because the phase-specific updates differ, forgetting phase changes
-- the next observable.  This is the exact finite witness for:
--
--   observable equality /= dynamical equivalence.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Foundations.DepthWheelGradedDynamics as Graded
import DASHI.Physics.Closure.SSPPrimeLane369DepthWheelCantorBridge as Wheel
import DASHI.Core.GradedProvenanceDynamicalSystemExact as GP

flip : Bool → Bool
flip false = true
flip true = false

hiddenPhaseWheel : Graded.GradedDepthWheelSystem
hiddenPhaseWheel =
  Graded.gradedDepthWheelSystem
    (λ phase → Bool)
    flip
    (λ x → x)
    (λ x → x)

hiddenPhaseSystem : GP.GradedProvenanceSystem
hiddenPhaseSystem =
  GP.gradedProvenanceSystem
    hiddenPhaseWheel
    Bool
    Wheel.DepthWheelPhase
    (GP.PackedState hiddenPhaseWheel)
    observe
    GP.grade
    (λ x → x)
    (λ observation receipt → receipt)
    (λ x → refl)
  where
    observe : GP.PackedState hiddenPhaseWheel → Bool
    observe (GP.at0 x) = x
    observe (GP.at1 x) = x
    observe (GP.at2 x) = x

leftState rightState : GP.PackedState hiddenPhaseWheel
leftState = GP.at0 false
rightState = GP.at1 false

sameCurrentObservation :
  GP.observe hiddenPhaseSystem leftState
  ≡ GP.observe hiddenPhaseSystem rightState
sameCurrentObservation = refl

nextObservationsDiffer :
  GP.observe hiddenPhaseSystem (GP.step hiddenPhaseWheel leftState)
  ≡ GP.observe hiddenPhaseSystem (GP.step hiddenPhaseWheel rightState) → ⊥
nextObservationsDiffer ()

hiddenPhaseIsDynamicallyRelevant : GP.DynamicInsufficiencyWitness hiddenPhaseSystem
hiddenPhaseIsDynamicallyRelevant =
  GP.dynamicInsufficiencyWitness
    leftState
    rightState
    sameCurrentObservation
    nextObservationsDiffer

noPhaseErasingCoarseStep :
  GP.DynamicallySufficientObservation hiddenPhaseSystem → ⊥
noPhaseErasingCoarseStep safe =
  GP.dynamicInsufficiencyContradictsSufficiency safe hiddenPhaseIsDynamicallyRelevant
