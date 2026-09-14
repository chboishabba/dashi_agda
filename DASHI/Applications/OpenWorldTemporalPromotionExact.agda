module DASHI.Applications.OpenWorldTemporalPromotionExact where

open import DASHI.Core.Prelude

import DASHI.Core.QueryIndexedProjectionAdequacyExact as Adequacy

------------------------------------------------------------------------
-- OPEN-WORLD TEMPORAL KNOWLEDGE / PROMOTION DISCIPLINE
--
-- High-value boundaries:
--   confidence != novelty status
--   unknown-at-encounter != low confidence
--   novelty detection != continual learning
--   later recognition does not rewrite the earlier observation state
--   reported score != held-out evaluation validity
------------------------------------------------------------------------

uncertaintyEqualsUnknown : Bool
uncertaintyEqualsUnknown = false

unknownRequiresLowConfidence : Bool
unknownRequiresLowConfidence = false

noveltyDetectionEqualsContinualLearning : Bool
noveltyDetectionEqualsContinualLearning = false

laterRecognitionRewritesEncounterState : Bool
laterRecognitionRewritesEncounterState = false

testTunedThresholdCountsAsHeldOut : Bool
testTunedThresholdCountsAsHeldOut = false

------------------------------------------------------------------------
-- I. Confidence alone is inadequate for novelty.
------------------------------------------------------------------------

data NoveltyWorld : Set where
  knownSameConfidence : NoveltyWorld
  novelSameConfidence : NoveltyWorld

data ConfidenceSurface : Set where
  sameConfidence : ConfidenceSurface

data NoveltyQuery : Set where
  confidenceQuery : NoveltyQuery
  noveltyStatusQuery : NoveltyQuery

data NoveltyAnswer : Set where
  confidenceObserved : NoveltyAnswer
  knownStatus : NoveltyAnswer
  unknownStatus : NoveltyAnswer

confidenceOnlyProjection : NoveltyWorld → ConfidenceSurface
confidenceOnlyProjection world = sameConfidence

noveltyAnswer : NoveltyQuery → NoveltyWorld → NoveltyAnswer
noveltyAnswer confidenceQuery world = confidenceObserved
noveltyAnswer noveltyStatusQuery knownSameConfidence = knownStatus
noveltyAnswer noveltyStatusQuery novelSameConfidence = unknownStatus

noveltySemantics :
  Adequacy.QuerySemantics NoveltyWorld NoveltyQuery NoveltyAnswer
noveltySemantics = Adequacy.querySemantics noveltyAnswer

confidenceOnlyNoveltyAdequacyDefect :
  Adequacy.QueryAdequacyDefect
    confidenceOnlyProjection
    noveltySemantics
    noveltyStatusQuery
confidenceOnlyNoveltyAdequacyDefect =
  Adequacy.queryAdequacyDefect
    knownSameConfidence
    novelSameConfidence
    refl
    (λ ())

confidenceAloneCannotDetermineNovelty :
  Adequacy.AdequateFor
    confidenceOnlyProjection
    noveltySemantics
    noveltyStatusQuery →
  ⊥
confidenceAloneCannotDetermineNovelty =
  Adequacy.queryAdequacyDefectBlocksFactorisation
    confidenceOnlyNoveltyAdequacyDefect

------------------------------------------------------------------------
-- II. Append-only temporal knowledge.
------------------------------------------------------------------------

data EncounterStatus : Set where
  encounterUnknown : EncounterStatus
  encounterKnown : EncounterStatus

data LaterStatus : Set where
  stillUnknownLater : LaterStatus
  recognizedLater : LaterStatus

data SemanticLabelState : Set where
  noSemanticLabelYet : SemanticLabelState
  laterSemanticLabel : SemanticLabelState

record TemporalKnowledgeReceipt : Set where
  constructor temporalKnowledgeReceipt
  field
    encounterStatus : EncounterStatus
    laterStatus : LaterStatus
    encounterLabelState : SemanticLabelState
    laterLabelState : SemanticLabelState
    encounterStateRetained : Bool
    encounterStateRetainedIsTrue : encounterStateRetained ≡ true
    laterLabelDoesNotRewriteEncounter : Bool
    laterLabelDoesNotRewriteEncounterIsTrue :
      laterLabelDoesNotRewriteEncounter ≡ true

open TemporalKnowledgeReceipt public

canonicalUnknownThenRecognizedReceipt : TemporalKnowledgeReceipt
canonicalUnknownThenRecognizedReceipt =
  temporalKnowledgeReceipt
    encounterUnknown
    recognizedLater
    noSemanticLabelYet
    laterSemanticLabel
    true refl
    true refl

------------------------------------------------------------------------
-- III. Novelty handling alone is not continual learning.
------------------------------------------------------------------------

data AdaptationWorld : Set where
  detectsNoveltyNoLearning : AdaptationWorld
  detectsNoveltyAndLearns : AdaptationWorld

data NoveltyHandlingSurface : Set where
  sameNoveltyDetection : NoveltyHandlingSurface

data AdaptationQuery : Set where
  noveltyDetectedQuery : AdaptationQuery
  continualLearningQuery : AdaptationQuery

data AdaptationAnswer : Set where
  noveltyDetectedAnswer : AdaptationAnswer
  noContinualLearningAnswer : AdaptationAnswer
  continualLearningAnswer : AdaptationAnswer

noveltyHandlingProjection : AdaptationWorld → NoveltyHandlingSurface
noveltyHandlingProjection world = sameNoveltyDetection

adaptationAnswer : AdaptationQuery → AdaptationWorld → AdaptationAnswer
adaptationAnswer noveltyDetectedQuery world = noveltyDetectedAnswer
adaptationAnswer continualLearningQuery detectsNoveltyNoLearning =
  noContinualLearningAnswer
adaptationAnswer continualLearningQuery detectsNoveltyAndLearns =
  continualLearningAnswer

adaptationSemantics :
  Adequacy.QuerySemantics AdaptationWorld AdaptationQuery AdaptationAnswer
adaptationSemantics = Adequacy.querySemantics adaptationAnswer

noveltyHandlingContinualLearningAdequacyDefect :
  Adequacy.QueryAdequacyDefect
    noveltyHandlingProjection
    adaptationSemantics
    continualLearningQuery
noveltyHandlingContinualLearningAdequacyDefect =
  Adequacy.queryAdequacyDefect
    detectsNoveltyNoLearning
    detectsNoveltyAndLearns
    refl
    (λ ())

noveltyDetectionCannotDetermineContinualLearning :
  Adequacy.AdequateFor
    noveltyHandlingProjection
    adaptationSemantics
    continualLearningQuery →
  ⊥
noveltyDetectionCannotDetermineContinualLearning =
  Adequacy.queryAdequacyDefectBlocksFactorisation
    noveltyHandlingContinualLearningAdequacyDefect

------------------------------------------------------------------------
-- IV. Reported metric alone is inadequate for evaluation validity.
------------------------------------------------------------------------

data EvaluationWorld : Set where
  frozenBeforeHeldOut : EvaluationWorld
  tunedOnHeldOut : EvaluationWorld

data ReportedScoreSurface : Set where
  sameReportedScore : ReportedScoreSurface

data EvaluationProtocolSurface : Set where
  frozenProtocol : EvaluationProtocolSurface
  testTunedProtocol : EvaluationProtocolSurface

data EvaluationQuery : Set where
  scoreQuery : EvaluationQuery
  heldOutProtocolQuery : EvaluationQuery

data EvaluationAnswer : Set where
  scoreObserved : EvaluationAnswer
  heldOutValid : EvaluationAnswer
  heldOutInvalid : EvaluationAnswer

reportedScoreProjection : EvaluationWorld → ReportedScoreSurface
reportedScoreProjection world = sameReportedScore

evaluationProtocolProjection : EvaluationWorld → EvaluationProtocolSurface
evaluationProtocolProjection frozenBeforeHeldOut = frozenProtocol
evaluationProtocolProjection tunedOnHeldOut = testTunedProtocol

evaluationAnswer : EvaluationQuery → EvaluationWorld → EvaluationAnswer
evaluationAnswer scoreQuery world = scoreObserved
evaluationAnswer heldOutProtocolQuery frozenBeforeHeldOut = heldOutValid
evaluationAnswer heldOutProtocolQuery tunedOnHeldOut = heldOutInvalid

evaluationSemantics :
  Adequacy.QuerySemantics EvaluationWorld EvaluationQuery EvaluationAnswer
evaluationSemantics = Adequacy.querySemantics evaluationAnswer

reportedScoreOnlyAdequacyDefect :
  Adequacy.QueryAdequacyDefect
    reportedScoreProjection
    evaluationSemantics
    heldOutProtocolQuery
reportedScoreOnlyAdequacyDefect =
  Adequacy.queryAdequacyDefect
    frozenBeforeHeldOut
    tunedOnHeldOut
    refl
    (λ ())

reportedScoreCannotDetermineHeldOutValidity :
  Adequacy.AdequateFor
    reportedScoreProjection
    evaluationSemantics
    heldOutProtocolQuery →
  ⊥
reportedScoreCannotDetermineHeldOutValidity =
  Adequacy.queryAdequacyDefectBlocksFactorisation
    reportedScoreOnlyAdequacyDefect

------------------------------------------------------------------------
-- V. Promotion ladder.  Each stage is an evidentiary status, not a license to
-- skip to identity, continual-learning, or operational-authority conclusions.
------------------------------------------------------------------------

data PromotionStage : Set where
  observationStage : PromotionStage
  noveltyStage : PromotionStage
  characterizationStage : PromotionStage
  semanticIdentityStage : PromotionStage
  continualLearningStage : PromotionStage
  operationalAuthorityStage : PromotionStage

record OpenWorldPromotionReceipt : Set where
  constructor openWorldPromotionReceipt
  field
    currentStage : PromotionStage
    provenanceRetained : Bool
    provenanceRetainedIsTrue : provenanceRetained ≡ true
    laterStageMayRewriteEarlierEvidence : Bool
    laterStageMayRewriteEarlierEvidenceIsFalse :
      laterStageMayRewriteEarlierEvidence ≡ false
    stageCreatesOperationalAuthority : Bool
    stageCreatesOperationalAuthorityIsFalse :
      stageCreatesOperationalAuthority ≡ false

open OpenWorldPromotionReceipt public

mkNonPromotingOpenWorldReceipt : PromotionStage → OpenWorldPromotionReceipt
mkNonPromotingOpenWorldReceipt stage =
  openWorldPromotionReceipt stage true refl false refl false refl

noveltyObservationReceipt : OpenWorldPromotionReceipt
noveltyObservationReceipt = mkNonPromotingOpenWorldReceipt noveltyStage

characterizedUnknownReceipt : OpenWorldPromotionReceipt
characterizedUnknownReceipt = mkNonPromotingOpenWorldReceipt characterizationStage

laterSemanticIdentityReceipt : OpenWorldPromotionReceipt
laterSemanticIdentityReceipt = mkNonPromotingOpenWorldReceipt semanticIdentityStage

record OpenWorldTemporalPromotionBoundary : Set where
  constructor openWorldTemporalPromotionBoundary
  field
    confidenceEqualsNovelty : Bool
    confidenceEqualsNoveltyIsFalse : confidenceEqualsNovelty ≡ false
    laterKnowledgeRewritesEarlierObservation : Bool
    laterKnowledgeRewritesEarlierObservationIsFalse :
      laterKnowledgeRewritesEarlierObservation ≡ false
    noveltyDetectionEqualsLearning : Bool
    noveltyDetectionEqualsLearningIsFalse : noveltyDetectionEqualsLearning ≡ false
    metricValueEqualsEvaluationValidity : Bool
    metricValueEqualsEvaluationValidityIsFalse :
      metricValueEqualsEvaluationValidity ≡ false
    semanticIdentityEqualsOperationalAuthority : Bool
    semanticIdentityEqualsOperationalAuthorityIsFalse :
      semanticIdentityEqualsOperationalAuthority ≡ false

canonicalOpenWorldTemporalPromotionBoundary :
  OpenWorldTemporalPromotionBoundary
canonicalOpenWorldTemporalPromotionBoundary =
  openWorldTemporalPromotionBoundary
    false refl
    false refl
    false refl
    false refl
    false refl
