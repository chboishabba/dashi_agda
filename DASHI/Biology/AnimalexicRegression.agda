module DASHI.Biology.AnimalexicRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Biology.AnimalexicFormalSystemExact as Animal
import DASHI.Core.ConsumerGuidedReopenableRefinementExact as Refine
import DASHI.Core.DualEffectAdaptiveFidelityExact as Fidelity
import DASHI.Core.AssumptionIndexedReopeningExact as Reopen
import DASHI.Core.GenericFuturePartitionRefinementExact as Future

data TinyState : Set where
  left right afterLeft afterRight : TinyState

data TinyAction : Set where
  probe : TinyAction

data TinyObservation : Set where
  same leftResponse rightResponse : TinyObservation

observeTiny : TinyState → TinyObservation
observeTiny left = same
observeTiny right = same
observeTiny afterLeft = leftResponse
observeTiny afterRight = rightResponse

stepTiny : TinyAction → TinyState → TinyState
stepTiny probe left = afterLeft
stepTiny probe right = afterRight
stepTiny probe afterLeft = afterLeft
stepTiny probe afterRight = afterRight

leftResponseNotRightResponse : leftResponse ≡ rightResponse → ⊥
leftResponseNotRightResponse ()

tinyOneStepWitness :
  Refine.OneStepSeparatingWitness observeTiny stepTiny left right
tinyOneStepWitness =
  Refine.oneStepSeparatingWitness refl probe leftResponseNotRightResponse

tinyStatesEquivalentAtDepthZero :
  Future.RefinesToDepth zero observeTiny stepTiny left right
tinyStatesEquivalentAtDepthZero =
  Refine.oneStepWitnessGivesDepthZero tinyOneStepWitness

tinyStatesNotEquivalentAtDepthOne :
  Future.RefinesToDepth (suc zero) observeTiny stepTiny left right → ⊥
tinyStatesNotEquivalentAtDepthOne =
  Refine.oneStepWitnessRefutesDepthOne tinyOneStepWitness

data TinyChange : Set where
  cameraFailure : TinyChange

data TinyRoute : Set where
  visualRoute acousticRoute : TinyRoute

HitsTiny : TinyChange → TinyRoute → Set
HitsTiny cameraFailure visualRoute = ⊤
HitsTiny cameraFailure acousticRoute = ⊥

tinySupportSystem : Reopen.AlternativeSupportSystem TinyChange TinyRoute
tinySupportSystem =
  Reopen.alternativeSupportSystem HitsTiny routeLabel
  where
    routeLabel : TinyRoute → String
    routeLabel visualRoute = "visual"
    routeLabel acousticRoute = "acoustic"

acousticSurvivesCameraFailure :
  Reopen.SurvivingSupportRoute tinySupportSystem cameraFailure
acousticSurvivesCameraFailure =
  Reopen.survivingSupportRoute acousticRoute (λ hit → hit)

cameraFailureDoesNotGloballyInvalidate :
  Reopen.GloballyInvalidates tinySupportSystem cameraFailure → ⊥
cameraFailureDoesNotGloballyInvalidate =
  Reopen.survivingRouteRefutesGlobalInvalidation acousticSurvivesCameraFailure

data TinyWorld : Set where
  world0 : TinyWorld

data TinyProbe : Set where
  inspect : TinyProbe

data TinyEvidence : Set where
  observationGenerated : TinyEvidence

tinyDualSystem :
  Fidelity.DualEffectActionSystem TinyWorld TinyProbe TinyEvidence
tinyDualSystem =
  Fidelity.dualEffectActionSystem
    (λ _ → Fidelity.informationOnly)
    (λ _ state → state)
    (λ _ _ → observationGenerated)

tinyInspectIsInformationOnly :
  Fidelity.InformationOnly tinyDualSystem inspect
tinyInspectIsInformationOnly state = refl

tinyInspectPreservesWorld :
  Fidelity.nextState (Fidelity.executeDualEffect tinyDualSystem inspect world0)
  ≡ world0
tinyInspectPreservesWorld =
  Fidelity.informationOnlyPreservesWorld tinyInspectIsInformationOnly world0

animalEpistemicBoundaryRecorded : Animal.AnimalexicEpistemicBoundary
animalEpistemicBoundaryRecorded = Animal.canonicalAnimalexicEpistemicBoundary

animalDeliverableBoundaryRecorded : Animal.AnimalexicFormalDeliverableBoundary
animalDeliverableBoundaryRecorded = Animal.canonicalAnimalexicFormalDeliverableBoundary
