module DASHI.Cognition.PNF.GrokkingEquivalenceStrataExact where

open import DASHI.Core.Prelude

import DASHI.Cognition.PNF.LLMGrokkingLearningFutureExact as Grok
import DASHI.Core.FutureEquivalenceCurrentObservationExact as Current
import DASHI.Core.FutureObservationLanguageQuotientExact as Future

------------------------------------------------------------------------
-- GROKKING EQUIVALENCE STRATA
--
-- In this finite learner every state has perfect training fit.  Current task
-- behaviour is finer than training fit, and complete learning-future language
-- is finer again.  The two strictness witnesses are different pairs.
------------------------------------------------------------------------

TrainingEquivalent : Grok.LearningState → Grok.LearningState → Set
TrainingEquivalent left right = Grok.trainingFit left ≡ Grok.trainingFit right

TaskEquivalent : Grok.LearningState → Grok.LearningState → Set
TaskEquivalent left right =
  Grok.generalizationVisible left ≡ Grok.generalizationVisible right

LearningFutureEquivalent : Grok.LearningState → Grok.LearningState → Set₁
LearningFutureEquivalent left right =
  Future.FutureObservationEquivalent
    Grok.learningSystem Grok.generalizationVisible left right

------------------------------------------------------------------------
-- Inclusions.
------------------------------------------------------------------------

learningFutureImpliesTask :
  ∀ {left right} →
  LearningFutureEquivalent left right →
  TaskEquivalent left right
learningFutureImpliesTask = Current.futureEquivalentImpliesCurrentObservationEqual

taskImpliesTraining :
  ∀ {left right} →
  TaskEquivalent left right →
  TrainingEquivalent left right
taskImpliesTraining {Grok.memorizerBefore} {Grok.memorizerBefore} task = refl
taskImpliesTraining {Grok.memorizerBefore} {Grok.structuredBefore} task = refl
taskImpliesTraining {Grok.memorizerBefore} {Grok.memorizerAfter} task = refl
taskImpliesTraining {Grok.memorizerBefore} {Grok.structuredAfter} ()
taskImpliesTraining {Grok.structuredBefore} {Grok.memorizerBefore} task = refl
taskImpliesTraining {Grok.structuredBefore} {Grok.structuredBefore} task = refl
taskImpliesTraining {Grok.structuredBefore} {Grok.memorizerAfter} task = refl
taskImpliesTraining {Grok.structuredBefore} {Grok.structuredAfter} ()
taskImpliesTraining {Grok.memorizerAfter} {Grok.memorizerBefore} task = refl
taskImpliesTraining {Grok.memorizerAfter} {Grok.structuredBefore} task = refl
taskImpliesTraining {Grok.memorizerAfter} {Grok.memorizerAfter} task = refl
taskImpliesTraining {Grok.memorizerAfter} {Grok.structuredAfter} ()
taskImpliesTraining {Grok.structuredAfter} {Grok.memorizerBefore} ()
taskImpliesTraining {Grok.structuredAfter} {Grok.structuredBefore} ()
taskImpliesTraining {Grok.structuredAfter} {Grok.memorizerAfter} ()
taskImpliesTraining {Grok.structuredAfter} {Grok.structuredAfter} task = refl

------------------------------------------------------------------------
-- Strictness: same current task observation but different learning futures.
------------------------------------------------------------------------

structuredAndMemorizerCurrentTaskEquivalent :
  TaskEquivalent Grok.structuredBefore Grok.memorizerBefore
structuredAndMemorizerCurrentTaskEquivalent = refl

currentTaskEquivalenceDoesNotImplyLearningFuture :
  LearningFutureEquivalent Grok.structuredBefore Grok.memorizerBefore → ⊥
currentTaskEquivalenceDoesNotImplyLearningFuture =
  Grok.sameTrainingFitDoesNotImplyLearningFutureEquivalence

------------------------------------------------------------------------
-- Strictness: same training observation but different current task behaviour.
------------------------------------------------------------------------

postTrainingStatesRemainTrainingEquivalent :
  TrainingEquivalent Grok.structuredAfter Grok.memorizerAfter
postTrainingStatesRemainTrainingEquivalent = refl

trainingEquivalenceDoesNotImplyTaskEquivalence :
  TaskEquivalent Grok.structuredAfter Grok.memorizerAfter → ⊥
trainingEquivalenceDoesNotImplyTaskEquivalence ()

------------------------------------------------------------------------
-- Therefore, in this explicit finite learner:
--
--   learning-future equivalence  =>  current-task equivalence
--                                =>  training-fit equivalence,
--
-- and neither converse is valid.
------------------------------------------------------------------------
