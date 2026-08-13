module DASHI.Cognition.PNF.LSTMForgetGateFutureSafetyExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.AdmissibleReachability as Reachability
import DASHI.Core.FutureObservationLanguageQuotientExact as Future
import DASHI.Core.TypedDependencyCore as Dependency

------------------------------------------------------------------------
-- Source boundary.
--
-- Sepp Hochreiter and Jürgen Schmidhuber,
-- "Long Short-Term Memory", Neural Computation 9(8), 1735-1780 (1997),
-- DOI 10.1162/neco.1997.9.8.1735.
--
-- This finite model does not formalize LSTM real-valued gates.  It isolates the
-- future-safety question: a learned forgetting operation is valid only when the
-- forgotten coordinate cannot alter any declared future observation.
------------------------------------------------------------------------

lstmAuthor : String
lstmAuthor = "Sepp Hochreiter; Juergen Schmidhuber"

lstmTitle : String
lstmTitle = "Long Short-Term Memory"

lstmDOI : String
lstmDOI = "10.1162/neco.1997.9.8.1735"

record RecurrentState : Set where
  constructor recurrentState
  field
    visibleState : Bool
    cellMemory : Bool

open RecurrentState public

data RecurrentAction : Set where
  exposeMemory : RecurrentAction

leftHidden : RecurrentState
leftHidden = recurrentState false false

rightHidden : RecurrentState
rightHidden = recurrentState false true

currentVisibleStateEqual : visibleState leftHidden ≡ visibleState rightHidden
currentVisibleStateEqual = refl

forgetMemory : RecurrentState → RecurrentState
forgetMemory state = recurrentState (visibleState state) false

forgetGateCollapsesHiddenStates : forgetMemory leftHidden ≡ forgetMemory rightHidden
forgetGateCollapsesHiddenStates = refl

advanceRecurrent : RecurrentState → RecurrentState
advanceRecurrent state = recurrentState (cellMemory state) (cellMemory state)

recurrentObservation : RecurrentState → Bool
recurrentObservation = visibleState

futureFineObservationsDiffer :
  recurrentObservation (advanceRecurrent leftHidden)
  ≡ recurrentObservation (advanceRecurrent rightHidden) → ⊥
futureFineObservationsDiffer ()

record ExactRecurrentPost
    (before : RecurrentState)
    (action : RecurrentAction)
    (after : RecurrentState) : Set where
  constructor exactRecurrentPost
  field
    afterIsExact : after ≡ advanceRecurrent before

open ExactRecurrentPost public

recurrentSystem : Dependency.DependentActionSystem RecurrentState RecurrentAction
recurrentSystem = record
  { Precondition = λ state action → ⊤
  ; Postcondition = ExactRecurrentPost
  ; actionLabel = λ action → "expose retained memory"
  }

exposeAdmissible :
  (state : RecurrentState) →
  Dependency.AdmissibleAction recurrentSystem state exposeMemory
exposeAdmissible state = record
  { precondition = tt
  ; after = advanceRecurrent state
  ; postcondition = exactRecurrentPost refl
  ; dependencyReceipt = "deterministic memory-exposure continuation"
  }

exposeTrace : List RecurrentAction
exposeTrace = exposeMemory ∷ []

rightFutureExposesTrue :
  Future.FutureObservation
    recurrentSystem recurrentObservation rightHidden exposeTrace true
rightFutureExposesTrue =
  Future.futureObservation
    (advanceRecurrent rightHidden)
    (Reachability.executesCons
      (exposeAdmissible rightHidden)
      Reachability.executesNil)
    refl

leftCannotExposeTrue :
  Future.FutureObservation
    recurrentSystem recurrentObservation leftHidden exposeTrace true
  → ⊥
leftCannotExposeTrue
  (Future.futureObservation after
    (Reachability.executesCons admissible Reachability.executesNil)
    observationProof)
  with afterIsExact (Dependency.postcondition admissible)
... | refl = contradiction observationProof
  where
    contradiction : false ≡ true → ⊥
    contradiction ()

forgettingCurrentEqualityIsNotFutureSafety :
  Future.FutureObservationEquivalent
    recurrentSystem recurrentObservation rightHidden leftHidden
  → ⊥
forgettingCurrentEqualityIsNotFutureSafety equivalent =
  leftCannotExposeTrue
    (Future.forward
      (Future.sameFutureLanguage equivalent exposeTrace true)
      rightFutureExposesTrue)

------------------------------------------------------------------------
-- Exact reopening from the forgotten visible state plus retained cell receipt.
------------------------------------------------------------------------

memoryResidual : RecurrentState → Bool
memoryResidual = cellMemory

reopenForgotten : RecurrentState → Bool → RecurrentState
reopenForgotten forgotten residual =
  recurrentState (visibleState forgotten) residual

reopenForgetWithMemoryResidualExact :
  (state : RecurrentState) →
  reopenForgotten (forgetMemory state) (memoryResidual state) ≡ state
reopenForgetWithMemoryResidualExact (recurrentState visible memory) = refl

------------------------------------------------------------------------
-- Thus a forget gate is not certified by current-output equality.  Either the
-- erased coordinate must lie inside canonical future equivalence, or a residual
-- must retain enough information for the required reopening semantics.
------------------------------------------------------------------------
