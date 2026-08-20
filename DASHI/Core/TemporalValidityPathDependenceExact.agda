module DASHI.Core.TemporalValidityPathDependenceExact where

------------------------------------------------------------------------
-- PURPOSE
--
-- Two related environmental failure modes are made exact:
--
--   1. time/regime erasure can make a formerly calibrated projection invalid;
--   2. path/hysteresis erasure can make a present-state summary dynamically
--      unsafe even when the visible current coordinate is identical.
--
-- No particular shift detector or hysteresis model is claimed.  These finite
-- countermodels establish the information that a safe runtime must retain.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Core.ReopenableConsumerInterventionKernelExact as Core

------------------------------------------------------------------------
-- 1. Non-stationary calibration: the same input has a different target after a
--    regime change, so an epoch-erasing calibration surface cannot be exact.
------------------------------------------------------------------------

data Epoch : Set where
  trainingEpoch shiftedEpoch : Epoch

data Input : Set where
  sameInput : Input

data Target : Set where
  oldResponse shiftedResponse : Target

data TimedState : Set where
  oldState newState : TimedState

inputOf : TimedState → Input
inputOf oldState = sameInput
inputOf newState = sameInput

epochOf : TimedState → Epoch
epochOf oldState = trainingEpoch
epochOf newState = shiftedEpoch

targetOf : TimedState → Target
targetOf oldState = oldResponse
targetOf newState = shiftedResponse

timeErasureCalibrationDefect :
  Core.ConsumerDescentDefect inputOf targetOf
timeErasureCalibrationDefect =
  Core.consumerDescentDefect oldState newState refl impossible
  where
    impossible : oldResponse ≡ shiftedResponse → ⊥
    impossible ()

data TimeAwareSurface : Set where
  trainingSurface shiftedSurface : TimeAwareSurface

timeAwareProject : TimedState → TimeAwareSurface
timeAwareProject oldState = trainingSurface
timeAwareProject newState = shiftedSurface

timeAwareTarget : TimeAwareSurface → Target
timeAwareTarget trainingSurface = oldResponse
timeAwareTarget shiftedSurface = shiftedResponse

timeAwareCalibrationDescends :
  Core.ConsumerDescent timeAwareProject targetOf
timeAwareCalibrationDescends = Core.consumerDescent timeAwareTarget proof
  where
    proof : ∀ state → targetOf state ≡ timeAwareTarget (timeAwareProject state)
    proof oldState = refl
    proof newState = refl

------------------------------------------------------------------------
-- 2. Path dependence / hysteresis: equal visible present state need not support
--    a common future transition after hidden history is erased.
------------------------------------------------------------------------

data FineMemoryState : Set where
  driedThenWet wettedThenWet : FineMemoryState

data VisibleState : Set where
  currentlyWet : VisibleState

data FineAfter : Set where
  rapidDrain slowDrain : FineAfter

data CoarseAfter : Set where
  onePredictedDrainClass : CoarseAfter

forgetHistory : FineMemoryState → VisibleState
forgetHistory driedThenWet = currentlyWet
forgetHistory wettedThenWet = currentlyWet

fineResponse : FineMemoryState → FineAfter
fineResponse driedThenWet = rapidDrain
fineResponse wettedThenWet = slowDrain

forgetFineAfter : FineAfter → CoarseAfter
forgetFineAfter rapidDrain = onePredictedDrainClass
forgetFineAfter slowDrain = onePredictedDrainClass

coarseResponse : VisibleState → CoarseAfter
coarseResponse currentlyWet = onePredictedDrainClass

-- The coarse response happens to commute for this deliberately coarse consumer.
coarseDrainIntertwines :
  Core.Intertwiner forgetHistory forgetFineAfter fineResponse coarseResponse
coarseDrainIntertwines = Core.intertwiner proof
  where
    proof : ∀ state →
      forgetFineAfter (fineResponse state) ≡ coarseResponse (forgetHistory state)
    proof driedThenWet = refl
    proof wettedThenWet = refl

-- But a consumer that needs the actual response cannot descend through the
-- present-moisture projection.  This is the exact hysteresis defect.
fineOutcomeDoesNotDescendThroughPresentState :
  Core.ConsumerDescentDefect forgetHistory fineResponse
fineOutcomeDoesNotDescendThroughPresentState =
  Core.consumerDescentDefect driedThenWet wettedThenWet refl impossible
  where
    impossible : rapidDrain ≡ slowDrain → ⊥
    impossible ()

record TemporalPathBoundary : Set where
  constructor temporalPathBoundary
  field
    trainingSupportNeedNotRemainValidAfterRegimeShift : Bool
    timeErasureCanBreakCalibrationDescent : Bool
    equalPresentSummaryNeedNotEraseHysteresis : Bool
    coarseConsumerSafetyNeedNotImplyFineConsumerSafety : Bool

canonicalTemporalPathBoundary : TemporalPathBoundary
canonicalTemporalPathBoundary =
  temporalPathBoundary true true true true
