module DASHI.Cognition.Teleodynamics.TeleodynamicLearningTransferExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Cognition.PNF.LearningProvenanceFutureExact as Provenance
import DASHI.Cognition.PNF.LLMGrokkingLearningFutureExact as Grok
import DASHI.Cognition.Teleodynamics.LLMGeometricPriorBridgeExact as LLM

------------------------------------------------------------------------
-- TELEODYNAMIC LEARNING-TRANSFER MODES
--
-- The proposed AI-transfer experiments distinguish parameter-changing training
-- from context-only interaction.  These are typed as different transition
-- classes.  Equal current outputs or parameters do not collapse optimizer /
-- curriculum provenance or future-learning language.
------------------------------------------------------------------------

data TransferTransition : Set where
  gradientTraining : TransferTransition
  contextOnlyInference : TransferTransition
  replayOrCurriculum : TransferTransition

record TeleodynamicLearningTransfer : Set where
  constructor teleodynamicLearningTransfer
  field
    teacherStateLabel : String
    studentStateLabel : String
    transition : TransferTransition
    currentObservableLabel : String
    futureLanguageLabel : String
    provenanceLabel : String

record LearningTransferBoundary : Set where
  constructor learningTransferBoundary
  field
    gradientAndICLSameTransition : Bool
    sameCurrentOutputMeansSameLearningState : Bool
    sameCurrentParametersMeansSameLearningFuture : Bool
    futureLanguageMustBeCheckedSeparately : Bool
    provenanceOwnerReused : Bool
    grokkingFutureOwnerReused : Bool

open LearningTransferBoundary public

canonicalLearningTransferBoundary : LearningTransferBoundary
canonicalLearningTransferBoundary =
  learningTransferBoundary false false false true true true

gradientTransfer contextTransfer : TeleodynamicLearningTransfer
gradientTransfer =
  teleodynamicLearningTransfer
    "teacher learner state"
    "student learner state"
    gradientTraining
    "current task/output observation"
    "post-interaction future observation language"
    "optimizer/curriculum/replay provenance retained"

contextTransfer =
  teleodynamicLearningTransfer
    "teacher learner state"
    "student learner state"
    contextOnlyInference
    "current task/output observation"
    "post-context future observation language"
    "context transition does not definitionally equal optimizer update"
