module DASHI.Cognition.PNF.NeuralBottleneckResidualFutureSafetyExact where

open import DASHI.Core.Prelude

import DASHI.Core.AdmissibleReachability as Reachability
import DASHI.Core.FutureObservationLanguageQuotientExact as Future
import DASHI.Core.TypedDependencyCore as Dependency

------------------------------------------------------------------------
-- FINITE NEURAL BOTTLENECK COUNTEREXAMPLE
--
-- Two fine states share one latent bottleneck code under the current task.  A
-- later context action exposes the hidden coordinate.  Retaining that coordinate
-- as a residual gives exact reopening and prevents terminalisation.
------------------------------------------------------------------------

record FineNeuralState : Set where
  constructor fineNeuralState
  field
    currentFeature : Bool
    hiddenFutureFeature : Bool

open FineNeuralState public

data NeuralAction : Set where
  exposeFutureFeature : NeuralAction

latentBottleneck : FineNeuralState → Bool
latentBottleneck state = currentFeature state

futureResidual : FineNeuralState → Bool
futureResidual state = hiddenFutureFeature state

leftFine rightFine : FineNeuralState
leftFine = fineNeuralState true false
rightFine = fineNeuralState true true

currentLatentEquality : latentBottleneck leftFine ≡ latentBottleneck rightFine
currentLatentEquality = refl

residualSeparatesFineStates : futureResidual leftFine ≡ futureResidual rightFine → ⊥
residualSeparatesFineStates ()

advance : FineNeuralState → FineNeuralState
advance state = fineNeuralState (hiddenFutureFeature state) (hiddenFutureFeature state)

visibleObservation : FineNeuralState → Bool
visibleObservation state = currentFeature state

record ExactNeuralPost
    (before : FineNeuralState)
    (action : NeuralAction)
    (after : FineNeuralState) : Set where
  constructor exactNeuralPost
  field afterIsExact : after ≡ advance before

open ExactNeuralPost public

neuralSystem : Dependency.DependentActionSystem FineNeuralState NeuralAction
neuralSystem = record
  { Precondition = λ state action → ⊤
  ; Postcondition = ExactNeuralPost
  ; actionLabel = λ action → "expose hidden future feature"
  }

exposeAdmissible :
  (state : FineNeuralState) →
  Dependency.AdmissibleAction neuralSystem state exposeFutureFeature
exposeAdmissible state = record
  { precondition = tt
  ; after = advance state
  ; postcondition = exactNeuralPost refl
  ; dependencyReceipt = "deterministic neural context transition"
  }

exposeTrace : List NeuralAction
exposeTrace = exposeFutureFeature ∷ []

rightFutureTrue :
  Future.FutureObservation neuralSystem visibleObservation rightFine exposeTrace true
rightFutureTrue =
  Future.futureObservation
    (advance rightFine)
    (Reachability.executesCons (exposeAdmissible rightFine) Reachability.executesNil)
    refl

leftCannotReachTrue :
  Future.FutureObservation neuralSystem visibleObservation leftFine exposeTrace true → ⊥
leftCannotReachTrue
  (Future.futureObservation after
    (Reachability.executesCons admissible Reachability.executesNil)
    observationProof)
  with afterIsExact (Dependency.postcondition admissible)
... | refl = contradiction observationProof
  where
    contradiction : false ≡ true → ⊥
    contradiction ()

latentEqualityDoesNotImplyFutureSafety :
  Future.FutureObservationEquivalent
    neuralSystem visibleObservation leftFine rightFine → ⊥
latentEqualityDoesNotImplyFutureSafety equivalent =
  leftCannotReachTrue
    (Future.backward
      (Future.sameFutureLanguage equivalent exposeTrace true)
      rightFutureTrue)

------------------------------------------------------------------------
-- Residual-bearing bottleneck is exactly reopenable.
------------------------------------------------------------------------

reopenLatent : Bool → Bool → FineNeuralState
reopenLatent latent residual = fineNeuralState latent residual

reopenBottleneckWithResidualExact :
  (state : FineNeuralState) →
  reopenLatent (latentBottleneck state) (futureResidual state) ≡ state
reopenBottleneckWithResidualExact (fineNeuralState current hidden) = refl

------------------------------------------------------------------------
-- This is the NN analogue of hidden phase and the spoken telescope example:
-- current latent equality is weaker than canonical future equivalence.
------------------------------------------------------------------------
