module DASHI.Applications.OpenClosedWorldRecognitionExact where

open import DASHI.Core.Prelude

import DASHI.Core.QueryIndexedProjectionAdequacyExact as Adequacy

------------------------------------------------------------------------
-- CLOSED SET / OPEN SET / OPEN WORLD RECOGNITION
--
-- Repository-local carrier informed by the attributed literature atlas.
-- The levels are not synonyms:
--   closed set  : test categories are assumed known at training time
--   open set    : unknown test categories are admissible and may be rejected
--   open world  : open-set handling plus later incorporation of new classes
--   OWOD        : open-world handling plus object localization/detection
-- OOD detection is adjacent but not definitionally identical to OSR.
------------------------------------------------------------------------

data RecognitionRegime : Set where
  closedSet : RecognitionRegime
  openSet : RecognitionRegime
  openWorld : RecognitionRegime
  openWorldObjectDetection : RecognitionRegime

data Capability : Set where
  classifyKnown : Capability
  detectUnknown : Capability
  rejectUnknown : Capability
  incrementallyAddClass : Capability
  localizeObject : Capability
  retainPriorKnowledge : Capability

data CapabilityStatus : Set where
  required : CapabilityStatus
  permitted : CapabilityStatus
  notRequired : CapabilityStatus

capabilityStatus : RecognitionRegime → Capability → CapabilityStatus
capabilityStatus closedSet classifyKnown = required
capabilityStatus closedSet detectUnknown = notRequired
capabilityStatus closedSet rejectUnknown = notRequired
capabilityStatus closedSet incrementallyAddClass = notRequired
capabilityStatus closedSet localizeObject = notRequired
capabilityStatus closedSet retainPriorKnowledge = notRequired
capabilityStatus openSet classifyKnown = required
capabilityStatus openSet detectUnknown = required
capabilityStatus openSet rejectUnknown = required
capabilityStatus openSet incrementallyAddClass = notRequired
capabilityStatus openSet localizeObject = notRequired
capabilityStatus openSet retainPriorKnowledge = notRequired
capabilityStatus openWorld classifyKnown = required
capabilityStatus openWorld detectUnknown = required
capabilityStatus openWorld rejectUnknown = required
capabilityStatus openWorld incrementallyAddClass = required
capabilityStatus openWorld localizeObject = notRequired
capabilityStatus openWorld retainPriorKnowledge = required
capabilityStatus openWorldObjectDetection classifyKnown = required
capabilityStatus openWorldObjectDetection detectUnknown = required
capabilityStatus openWorldObjectDetection rejectUnknown = required
capabilityStatus openWorldObjectDetection incrementallyAddClass = required
capabilityStatus openWorldObjectDetection localizeObject = required
capabilityStatus openWorldObjectDetection retainPriorKnowledge = required

closedSetAssumesKnownTestClasses : Bool
closedSetAssumesKnownTestClasses = true

openSetAllowsUnknownTestClasses : Bool
openSetAllowsUnknownTestClasses = true

openSetRequiresIncrementalIncorporation : Bool
openSetRequiresIncrementalIncorporation = false

openWorldRequiresUnknownHandlingAndIncrementalLearning : Bool
openWorldRequiresUnknownHandlingAndIncrementalLearning = true

openWorldObjectDetectionRequiresLocalization : Bool
openWorldObjectDetectionRequiresLocalization = true

oodDetectionEqualsOpenSetRecognition : Bool
oodDetectionEqualsOpenSetRecognition = false

openSetEqualsOpenWorld : Bool
openSetEqualsOpenWorld = false

unknownRecognitionCreatesKnownIdentity : Bool
unknownRecognitionCreatesKnownIdentity = false

incrementalAdditionRetroactivelyValidatesPriorIdentity : Bool
incrementalAdditionRetroactivelyValidatesPriorIdentity = false

------------------------------------------------------------------------
-- Exact finite witness I: closed-set output forces a known label where an
-- open-set observer can preserve 'unknown'.  Thus a closed label surface is
-- inadequate for the query "was this observation outside the known classes?"
------------------------------------------------------------------------

data RecognitionWorld : Set where
  knownAlphaWorld : RecognitionWorld
  novelWorld : RecognitionWorld

data ClosedLabel : Set where
  alphaLabel : ClosedLabel

data OpenLabel : Set where
  knownAlphaLabel : OpenLabel
  unknownLabel : OpenLabel

data RecognitionQuery : Set where
  closedClassificationQuery : RecognitionQuery
  noveltyQuery : RecognitionQuery

data RecognitionAnswer : Set where
  alphaAnswer : RecognitionAnswer
  knownAnswer : RecognitionAnswer
  unknownAnswer : RecognitionAnswer

closedProjection : RecognitionWorld → ClosedLabel
closedProjection knownAlphaWorld = alphaLabel
closedProjection novelWorld = alphaLabel

openProjection : RecognitionWorld → OpenLabel
openProjection knownAlphaWorld = knownAlphaLabel
openProjection novelWorld = unknownLabel

recognitionAnswer : RecognitionQuery → RecognitionWorld → RecognitionAnswer
recognitionAnswer closedClassificationQuery world = alphaAnswer
recognitionAnswer noveltyQuery knownAlphaWorld = knownAnswer
recognitionAnswer noveltyQuery novelWorld = unknownAnswer

recognitionSemantics :
  Adequacy.QuerySemantics RecognitionWorld RecognitionQuery RecognitionAnswer
recognitionSemantics = Adequacy.querySemantics recognitionAnswer

closedSurfaceNoveltyAdequacyDefect :
  Adequacy.QueryAdequacyDefect
    closedProjection
    recognitionSemantics
    noveltyQuery
closedSurfaceNoveltyAdequacyDefect =
  Adequacy.queryAdequacyDefect
    knownAlphaWorld
    novelWorld
    refl
    (λ ())

closedSurfaceCannotDetermineNovelty :
  Adequacy.AdequateFor closedProjection recognitionSemantics noveltyQuery → ⊥
closedSurfaceCannotDetermineNovelty =
  Adequacy.queryAdequacyDefectBlocksFactorisation
    closedSurfaceNoveltyAdequacyDefect

openNoveltyAnswer : OpenLabel → RecognitionAnswer
openNoveltyAnswer knownAlphaLabel = knownAnswer
openNoveltyAnswer unknownLabel = unknownAnswer

openSurfaceDeterminesNovelty :
  Adequacy.AdequateFor openProjection recognitionSemantics noveltyQuery
openSurfaceDeterminesNovelty =
  Adequacy.factorsForQuery
    openNoveltyAnswer
    (λ { knownAlphaWorld → refl
       ; novelWorld → refl
       })

------------------------------------------------------------------------
-- Exact finite witness II: open-set unknown recognition does not determine
-- whether the system can subsequently incorporate the novel class.  Therefore
-- open-set recognition is not equivalent to open-world learning.
------------------------------------------------------------------------

data LearningWorld : Set where
  rejectsUnknownOnly : LearningWorld
  rejectsThenLearns : LearningWorld

data UnknownHandlingSurface : Set where
  sameUnknownHandled : UnknownHandlingSurface

data LearningQuery : Set where
  unknownHandledQuery : LearningQuery
  incrementalLearningQuery : LearningQuery

data LearningAnswer : Set where
  unknownHandledAnswer : LearningAnswer
  noIncrementalLearning : LearningAnswer
  incrementalLearningPresent : LearningAnswer

unknownHandlingProjection : LearningWorld → UnknownHandlingSurface
unknownHandlingProjection world = sameUnknownHandled

learningAnswer : LearningQuery → LearningWorld → LearningAnswer
learningAnswer unknownHandledQuery world = unknownHandledAnswer
learningAnswer incrementalLearningQuery rejectsUnknownOnly = noIncrementalLearning
learningAnswer incrementalLearningQuery rejectsThenLearns = incrementalLearningPresent

learningSemantics :
  Adequacy.QuerySemantics LearningWorld LearningQuery LearningAnswer
learningSemantics = Adequacy.querySemantics learningAnswer

openSetSurfaceOpenWorldAdequacyDefect :
  Adequacy.QueryAdequacyDefect
    unknownHandlingProjection
    learningSemantics
    incrementalLearningQuery
openSetSurfaceOpenWorldAdequacyDefect =
  Adequacy.queryAdequacyDefect
    rejectsUnknownOnly
    rejectsThenLearns
    refl
    (λ ())

openSetHandlingCannotDetermineOpenWorldLearning :
  Adequacy.AdequateFor
    unknownHandlingProjection
    learningSemantics
    incrementalLearningQuery →
  ⊥
openSetHandlingCannotDetermineOpenWorldLearning =
  Adequacy.queryAdequacyDefectBlocksFactorisation
    openSetSurfaceOpenWorldAdequacyDefect

------------------------------------------------------------------------
-- OOD/OSR boundary: keep task identity separate.
------------------------------------------------------------------------

data UnknownTask : Set where
  outOfDistributionDetection : UnknownTask
  openSetRecognition : UnknownTask
  openWorldRecognition : UnknownTask

data TaskQuestion : Set where
  distributionMembershipQuestion : TaskQuestion
  semanticKnownUnknownQuestion : TaskQuestion
  incrementalKnowledgeQuestion : TaskQuestion

addresses : UnknownTask → TaskQuestion → Bool
addresses outOfDistributionDetection distributionMembershipQuestion = true
addresses outOfDistributionDetection semanticKnownUnknownQuestion = false
addresses outOfDistributionDetection incrementalKnowledgeQuestion = false
addresses openSetRecognition distributionMembershipQuestion = false
addresses openSetRecognition semanticKnownUnknownQuestion = true
addresses openSetRecognition incrementalKnowledgeQuestion = false
addresses openWorldRecognition distributionMembershipQuestion = false
addresses openWorldRecognition semanticKnownUnknownQuestion = true
addresses openWorldRecognition incrementalKnowledgeQuestion = true

record OpenClosedWorldBoundary : Set where
  constructor openClosedWorldBoundary
  field
    closedSetEqualsOpenSet : Bool
    closedSetEqualsOpenSetIsFalse : closedSetEqualsOpenSet ≡ false
    openSetEqualsOpenWorldBoundary : Bool
    openSetEqualsOpenWorldBoundaryIsFalse : openSetEqualsOpenWorldBoundary ≡ false
    oodEqualsOSRBoundary : Bool
    oodEqualsOSRBoundaryIsFalse : oodEqualsOSRBoundary ≡ false
    noveltyLabelEqualsIdentity : Bool
    noveltyLabelEqualsIdentityIsFalse : noveltyLabelEqualsIdentity ≡ false
    laterClassAdditionRewritesEarlierEvidence : Bool
    laterClassAdditionRewritesEarlierEvidenceIsFalse :
      laterClassAdditionRewritesEarlierEvidence ≡ false

canonicalOpenClosedWorldBoundary : OpenClosedWorldBoundary
canonicalOpenClosedWorldBoundary =
  openClosedWorldBoundary false refl false refl false refl false refl false refl
