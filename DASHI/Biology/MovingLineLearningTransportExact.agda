module DASHI.Biology.MovingLineLearningTransportExact where

open import DASHI.Core.Prelude
open import Data.Vec using (Vec) renaming ([] to vnil; _∷_ to _vcons_)

import DASHI.Cognition.PNF.MemoryFibre as Memory
import DASHI.Biology.DASHIYijingTernaryDivinationExact as Yijing

------------------------------------------------------------------------
-- Moving-line inversion remains a symbolic projection.  The underlying
-- psychogeographic transition is an independently typed memory/learning
-- operator, and compatibility is a theorem about the observation surface.
------------------------------------------------------------------------

data PreservingLearningMode : Set where
  revaluationMode : Nat → PreservingLearningMode
  habituationMode : PreservingLearningMode
  inhibitoryExtinctionMode : PreservingLearningMode
  phaseRealignmentMode : Nat → PreservingLearningMode

applyLearning : PreservingLearningMode → Memory.MemoryFibre → Memory.MemoryFibre
applyLearning (revaluationMode value) memory = Memory.revalue memory value
applyLearning habituationMode memory = Memory.habituate memory
applyLearning inhibitoryExtinctionMode memory =
  Memory.extinguishActionDominance memory
applyLearning (phaseRealignmentMode phase) memory =
  Memory.realignPhase memory phase

learningPreservesRememberedEvent :
  ∀ mode memory →
  Memory.rememberedEvent (applyLearning mode memory)
  ≡ Memory.rememberedEvent memory
learningPreservesRememberedEvent (revaluationMode value) memory =
  Memory.revaluePreservesRememberedEvent memory value
learningPreservesRememberedEvent habituationMode memory =
  Memory.habituationPreservesRememberedEvent memory
learningPreservesRememberedEvent inhibitoryExtinctionMode memory =
  Memory.extinctionPreservesRememberedEvent memory
learningPreservesRememberedEvent (phaseRealignmentMode phase) memory = refl

record PlaceLearningState : Set where
  constructor placeLearningState
  field
    memory : Memory.MemoryFibre
    observedHexagram : Yijing.TernaryHexagram
    routeRevision : Nat

open PlaceLearningState public

applyMovingLearning :
  Vec Bool 6 → PreservingLearningMode → PlaceLearningState → PlaceLearningState
applyMovingLearning mask mode state =
  placeLearningState
    (applyLearning mode (memory state))
    (Yijing.applyMovingMask mask (observedHexagram state))
    (suc (routeRevision state))

movingProjectionCommutes :
  ∀ mask mode state →
  observedHexagram (applyMovingLearning mask mode state)
  ≡ Yijing.applyMovingMask mask (observedHexagram state)
movingProjectionCommutes mask mode state = refl

movingLearningPreservesRememberedEvent :
  ∀ mask mode state →
  Memory.rememberedEvent (memory (applyMovingLearning mask mode state))
  ≡ Memory.rememberedEvent (memory state)
movingLearningPreservesRememberedEvent mask mode state =
  learningPreservesRememberedEvent mode (memory state)

canonicalMovingLearningResult :
  ∀ memory →
  observedHexagram
    (applyMovingLearning
      Yijing.canonicalMovingMask
      inhibitoryExtinctionMode
      (placeLearningState memory Yijing.canonicalTernaryHexagram 0))
  ≡ Yijing.canonicalResultingHexagram
canonicalMovingLearningResult memory = Yijing.canonicalMovingResultIsExact

canonicalMovingLearningIncrementsRevision :
  ∀ memory →
  routeRevision
    (applyMovingLearning
      Yijing.canonicalMovingMask
      inhibitoryExtinctionMode
      (placeLearningState memory Yijing.canonicalTernaryHexagram 0))
  ≡ 1
canonicalMovingLearningIncrementsRevision memory = refl

record MovingLineLearningBoundary : Set where
  constructor movingLineLearningBoundary
  field
    psychologicalChangeIsLiterallySignInversion : Bool
    psychologicalChangeIsLiterallySignInversionIsFalse :
      psychologicalChangeIsLiterallySignInversion ≡ false
    symbolicCompatibilityRequiresTypedOperator : Bool
    symbolicCompatibilityRequiresTypedOperatorIsTrue :
      symbolicCompatibilityRequiresTypedOperator ≡ true
    resultingHexagramAloneProvesHealing : Bool
    resultingHexagramAloneProvesHealingIsFalse :
      resultingHexagramAloneProvesHealing ≡ false
    memoryPreservationIsEventErasure : Bool
    memoryPreservationIsEventErasureIsFalse :
      memoryPreservationIsEventErasure ≡ false

canonicalMovingLineLearningBoundary : MovingLineLearningBoundary
canonicalMovingLineLearningBoundary =
  movingLineLearningBoundary false refl true refl false refl false refl
