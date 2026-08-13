module DASHI.Cognition.PNF.LLMGrokkingLearningFutureExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.AdmissibleReachability as Reachability
import DASHI.Core.FutureObservationLanguageQuotientExact as Future
import DASHI.Core.TypedDependencyCore as Dependency

------------------------------------------------------------------------
-- Source boundary.
--
-- Alethea Power, Yuri Burda, Harri Edwards, Igor Babuschkin, Vedant Misra,
-- "Grokking: Generalization Beyond Overfitting on Small Algorithmic Datasets",
-- arXiv:2201.02177.  No DOI asserted here.
--
-- Neel Nanda, Lawrence Chan, Tom Lieberum, Jess Smith, Jacob Steinhardt,
-- "Progress measures for grokking via mechanistic interpretability",
-- arXiv:2301.05217.  No DOI asserted here.
--
-- The finite model below proves only a structural phenomenon: equal coarse
-- training observations can conceal different learning futures.
------------------------------------------------------------------------

powerGrokkingTitle : String
powerGrokkingTitle = "Grokking: Generalization Beyond Overfitting on Small Algorithmic Datasets"

nandaGrokkingTitle : String
nandaGrokkingTitle = "Progress measures for grokking via mechanistic interpretability"

data LearningState : Set where
  memorizerBefore structuredBefore memorizerAfter structuredAfter : LearningState

data LearningAction : Set where
  continueTraining : LearningAction

trainingFit : LearningState → Bool
trainingFit memorizerBefore = true
trainingFit structuredBefore = true
trainingFit memorizerAfter = true
trainingFit structuredAfter = true

generalizationVisible : LearningState → Bool
generalizationVisible memorizerBefore = false
generalizationVisible structuredBefore = false
generalizationVisible memorizerAfter = false
generalizationVisible structuredAfter = true

latentAlgorithmicProgress : LearningState → Bool
latentAlgorithmicProgress memorizerBefore = false
latentAlgorithmicProgress structuredBefore = true
latentAlgorithmicProgress memorizerAfter = false
latentAlgorithmicProgress structuredAfter = true

currentTrainingObservationCollapsesStates :
  trainingFit memorizerBefore ≡ trainingFit structuredBefore
currentTrainingObservationCollapsesStates = refl

currentGeneralizationObservationAlsoCollapsesStates :
  generalizationVisible memorizerBefore ≡ generalizationVisible structuredBefore
currentGeneralizationObservationAlsoCollapsesStates = refl

progressResidualSeparatesStates :
  latentAlgorithmicProgress memorizerBefore
  ≡ latentAlgorithmicProgress structuredBefore → ⊥
progressResidualSeparatesStates ()

advanceLearning : LearningState → LearningState
advanceLearning memorizerBefore = memorizerAfter
advanceLearning structuredBefore = structuredAfter
advanceLearning memorizerAfter = memorizerAfter
advanceLearning structuredAfter = structuredAfter

record ExactLearningPost
    (before : LearningState)
    (action : LearningAction)
    (after : LearningState) : Set where
  constructor exactLearningPost
  field
    afterIsExact : after ≡ advanceLearning before

open ExactLearningPost public

learningSystem : Dependency.DependentActionSystem LearningState LearningAction
learningSystem = record
  { Precondition = λ state action → ⊤
  ; Postcondition = ExactLearningPost
  ; actionLabel = λ action → "continue training"
  }

continueAdmissible :
  (state : LearningState) →
  Dependency.AdmissibleAction learningSystem state continueTraining
continueAdmissible state = record
  { precondition = tt
  ; after = advanceLearning state
  ; postcondition = exactLearningPost refl
  ; dependencyReceipt = "deterministic finite learning continuation"
  }

continueTrace : List LearningAction
continueTrace = continueTraining ∷ []

structuredFutureGeneralizes :
  Future.FutureObservation
    learningSystem
    generalizationVisible
    structuredBefore
    continueTrace
    true
structuredFutureGeneralizes =
  Future.futureObservation
    structuredAfter
    (Reachability.executesCons
      (continueAdmissible structuredBefore)
      Reachability.executesNil)
    refl

memorizerCannotProduceTrueGeneralizationAfterTrace :
  Future.FutureObservation
    learningSystem
    generalizationVisible
    memorizerBefore
    continueTrace
    true
  → ⊥
memorizerCannotProduceTrueGeneralizationAfterTrace
  (Future.futureObservation after
    (Reachability.executesCons admissible Reachability.executesNil)
    observationProof)
  with afterIsExact (Dependency.postcondition admissible)
... | refl = contradiction observationProof
  where
    contradiction : false ≡ true → ⊥
    contradiction ()

sameTrainingFitDoesNotImplyLearningFutureEquivalence :
  Future.FutureObservationEquivalent
    learningSystem
    generalizationVisible
    structuredBefore
    memorizerBefore
  → ⊥
sameTrainingFitDoesNotImplyLearningFutureEquivalence equivalent =
  memorizerCannotProduceTrueGeneralizationAfterTrace
    (Future.forward
      (Future.sameFutureLanguage equivalent continueTrace true)
      structuredFutureGeneralizes)

------------------------------------------------------------------------
-- Exact lesson: the current loss/accuracy quotient can collapse states whose
-- future learning languages differ.  A progress residual may distinguish them
-- before the coarse behavioural observable changes.
------------------------------------------------------------------------
