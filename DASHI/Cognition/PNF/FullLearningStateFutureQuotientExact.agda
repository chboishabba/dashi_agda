module DASHI.Cognition.PNF.FullLearningStateFutureQuotientExact where

open import DASHI.Core.Prelude

data Parameter : Set where
  neutralParam positiveParam : Parameter

data Optimizer : Set where
  momentumLeft momentumRight : Optimizer

data Provenance : Set where
  curriculumA curriculumB : Provenance

data Replay : Set where
  replayCold replayWarm : Replay

data Batch : Set where
  commonBatch : Batch

record LearnerState : Set where
  constructor learnerState
  field
    parameter : Parameter
    optimizer : Optimizer
    provenance : Provenance
    replay : Replay

open LearnerState public

visibleModel : LearnerState → Parameter
visibleModel = parameter

update : Batch → LearnerState → LearnerState
update commonBatch (learnerState neutralParam momentumLeft provenance replay) =
  learnerState neutralParam momentumLeft provenance replay
update commonBatch (learnerState neutralParam momentumRight provenance replay) =
  learnerState positiveParam momentumRight provenance replay
update commonBatch state = state

leftLearner rightLearner : LearnerState
leftLearner = learnerState neutralParam momentumLeft curriculumA replayCold
rightLearner = learnerState neutralParam momentumRight curriculumB replayWarm

sameWeightsNow : visibleModel leftLearner ≡ visibleModel rightLearner
sameWeightsNow = refl

sameBatchDifferentLearningFuture :
  visibleModel (update commonBatch leftLearner)
  ≡ visibleModel (update commonBatch rightLearner) → ⊥
sameBatchDifferentLearningFuture ()

record LearningFutureDefect : Set where
  constructor learningFutureDefect
  field
    currentParameterEqual : visibleModel leftLearner ≡ visibleModel rightLearner
    futureParameterDifferent :
      visibleModel (update commonBatch leftLearner)
      ≡ visibleModel (update commonBatch rightLearner) → ⊥

canonicalLearningFutureDefect : LearningFutureDefect
canonicalLearningFutureDefect =
  learningFutureDefect sameWeightsNow sameBatchDifferentLearningFuture

record LearningResidual : Set where
  constructor learningResidualData
  field
    savedOptimizer : Optimizer
    savedProvenance : Provenance
    savedReplay : Replay

open LearningResidual public

learningResidual : LearnerState → LearningResidual
learningResidual state =
  learningResidualData
    (optimizer state)
    (provenance state)
    (replay state)

reopenLearner : Parameter → LearningResidual → LearnerState
reopenLearner parameter
  (learningResidualData optimizer provenance replay) =
  learnerState parameter optimizer provenance replay

learningResidualReopensExact :
  (state : LearnerState) →
  reopenLearner (visibleModel state) (learningResidual state) ≡ state
learningResidualReopensExact (learnerState parameter optimizer provenance replay) = refl

data Consumer : Set where
  inferenceConsumer continuedLearningConsumer : Consumer

consumerObservation : Consumer → LearnerState → Parameter
consumerObservation inferenceConsumer state = visibleModel state
consumerObservation continuedLearningConsumer state = visibleModel (update commonBatch state)

inferenceConsumerMergesCurrentLearners :
  consumerObservation inferenceConsumer leftLearner
  ≡ consumerObservation inferenceConsumer rightLearner
inferenceConsumerMergesCurrentLearners = refl

continuedLearningConsumerSeparatesThem :
  consumerObservation continuedLearningConsumer leftLearner
  ≡ consumerObservation continuedLearningConsumer rightLearner → ⊥
continuedLearningConsumerSeparatesThem ()
