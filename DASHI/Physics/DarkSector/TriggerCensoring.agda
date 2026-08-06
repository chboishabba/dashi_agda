module DASHI.Physics.DarkSector.TriggerCensoring where

open import DASHI.Core.Prelude
open import Data.Nat using (_≤ᵇ_)

import DASHI.Physics.DarkSector.DisplacedVertex as Vertex

------------------------------------------------------------------------
-- Online triggers are lossy observation channels on full detector events.

data TriggerDecision : Set where
  rejectEvent : TriggerDecision
  acceptEvent : TriggerDecision

promptTrigger : Vertex.VertexEvent → TriggerDecision
promptTrigger event with Vertex.vertexDisplacement event ≤ᵇ 1
... | true = acceptEvent
... | false = rejectEvent

llpTrigger : Vertex.VertexEvent → TriggerDecision
llpTrigger event with Vertex.isDisplacedVertex event
... | true = acceptEvent
... | false = rejectEvent

canonicalPromptTriggerRejectsDisplacedSignal :
  promptTrigger Vertex.canonicalDisplacedEvent ≡ rejectEvent
canonicalPromptTriggerRejectsDisplacedSignal = refl

canonicalLLPTriggerAcceptsDisplacedSignal :
  llpTrigger Vertex.canonicalDisplacedEvent ≡ acceptEvent
canonicalLLPTriggerAcceptsDisplacedSignal = refl

canonicalPromptTriggerAcceptsPromptControl :
  promptTrigger Vertex.canonicalPromptEvent ≡ acceptEvent
canonicalPromptTriggerAcceptsPromptControl = refl

------------------------------------------------------------------------
-- Finite acceptance factorisation.  A null recorded count at zero acceptance
-- cannot identify the underlying production rate.

recordedSignalCount : Nat → Nat → Nat → Nat
recordedSignalCount productionRate branchingWeight acceptanceWeight =
  productionRate * branchingWeight * acceptanceWeight

zeroAcceptanceErasesFiveEventSignal :
  recordedSignalCount 5 2 0 ≡ 0
zeroAcceptanceErasesFiveEventSignal = refl

zeroAcceptanceErasesNineEventSignal :
  recordedSignalCount 9 1 0 ≡ 0
zeroAcceptanceErasesNineEventSignal = refl

recordedNullDoesNotIdentifyProduction :
  recordedSignalCount 5 2 0
  ≡
  recordedSignalCount 9 1 0
recordedNullDoesNotIdentifyProduction = refl

nonzeroAcceptanceRetainsRateDifference :
  recordedSignalCount 5 2 1
  ≡
  10
  ×
  recordedSignalCount 9 1 1
  ≡
  9
nonzeroAcceptanceRetainsRateDifference = refl , refl

------------------------------------------------------------------------
-- Explicit signal and control channels.

data EventClass : Set where
  promptControl : EventClass
  displacedSignal : EventClass
  detectorOutside : EventClass

classEvent : EventClass → Vertex.VertexEvent
classEvent promptControl = Vertex.canonicalPromptEvent
classEvent displacedSignal = Vertex.canonicalDisplacedEvent
classEvent detectorOutside = Vertex.canonicalOutsideDetectorEvent

record TriggerCensoringBoundary : Set where
  constructor triggerCensoringBoundary
  field
    absenceFromRecordedDatasetImpliesAbsenceFromCollisions : Bool
    absenceFromRecordedDatasetImpliesAbsenceFromCollisionsIsFalse :
      absenceFromRecordedDatasetImpliesAbsenceFromCollisions ≡ false

    promptTriggerIsUnbiasedForDisplacedSignals : Bool
    promptTriggerIsUnbiasedForDisplacedSignalsIsFalse :
      promptTriggerIsUnbiasedForDisplacedSignals ≡ false

    displacedTriggerAcceptanceIsAutomaticallyOne : Bool
    displacedTriggerAcceptanceIsAutomaticallyOneIsFalse :
      displacedTriggerAcceptanceIsAutomaticallyOne ≡ false

open TriggerCensoringBoundary public

canonicalTriggerCensoringBoundary : TriggerCensoringBoundary
canonicalTriggerCensoringBoundary =
  triggerCensoringBoundary false refl false refl false refl
