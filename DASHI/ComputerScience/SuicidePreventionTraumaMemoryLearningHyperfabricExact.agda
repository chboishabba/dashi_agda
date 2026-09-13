module DASHI.ComputerScience.SuicidePreventionTraumaMemoryLearningHyperfabricExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.AdmissibleTransitionHyperfabricExact as Admissible
import DASHI.ComputerScience.WrongTypeAttributionFactorisationPlanningSnowballExact as WrongType
import DASHI.ComputerScience.SuicidePreventionProtectiveNarrativeWrongTypeIntersectionalExact as Prevention

------------------------------------------------------------------------
-- TRAUMA / MEMORY / LEARNING HYPERFABRIC
--
-- This owner extends the protective-narrative lane without turning personal
-- testimony into clinical authority.  The central object is consumer-indexed:
-- trauma history, remembered content, current accessibility, learned response,
-- relationship context, protective attachment, and communication suitability
-- are distinct axes.  No one projection is promoted to the others without a
-- factorisation receipt.
--
-- Attribution/snowball discipline:
--   * source identity, transcription, interpretation, and formalisation are
--     distinct coordinates;
--   * acquisition order may be opportunistic, but conclusion-payment order is
--     dependency-indexed;
--   * evidence is append-only; later evidence does not rewrite earlier source
--     state;
--   * creator gloss, family testimony, and research literature retain their
--     own source roles;
--   * a citation imports neither proof nor authority for claims it does not
--     directly own.
------------------------------------------------------------------------

data SourceKind : Set where
  personalCorrespondence : SourceKind
  familyTestimony : SourceKind
  socialMediaCreator : SourceKind
  primaryResearch : SourceKind
  professionalGuidance : SourceKind

record AttributedSource : Set where
  constructor attributed-source
  field
    authorOrAccount : String
    titleOrObject : String
    publicationContext : String
    persistentIdentifier : String
    sourceKind : SourceKind
    directClaimOwner : Bool
    transcriptionReviewed : Bool
    interpretationReviewed : Bool
    formalisationRelationship : String
open AttributedSource public

------------------------------------------------------------------------
-- INSTAGRAM SOURCE RECEIPT
--
-- We retain the account/video identity supplied by the user as a source
-- coordinate.  The social-media object remains creator interpretation unless
-- and until its own publication metadata and upstream citations are separately
-- verified.  This prevents account identity from silently becoming study
-- authorship or clinical authority.
------------------------------------------------------------------------

isaacInstagram : AttributedSource
isaacInstagram = attributed-source
  "@alltimeisaac / Isaac Sanders"
  "World Suicide Prevention Day video on staying alive / reasons for living"
  "Instagram social-video object supplied 2026-09-11"
  "video:DdHAaX2hi3Z"
  socialMediaCreator
  false
  true
  false
  "creator testimony and research-signposting source; not primary-study authority"

------------------------------------------------------------------------
-- JOHN / ALICE / FAMILY-SOURCE BOUNDARY
--
-- Prior project material contains family correspondence concerning trauma,
-- unwanted memories, distress, and relational context involving John, Alice,
-- and Johl.  We deliberately encode only the source-role grammar here: personal
-- correspondence may evidence that a person reported/expressed an experience,
-- but does not by itself establish a diagnosis, causal mechanism, memory
-- accuracy, or another person's mental state.
------------------------------------------------------------------------

johnFamilyCorrespondence : AttributedSource
johnFamilyCorrespondence = attributed-source
  "John Brown"
  "family correspondence concerning unwanted memories and relational distress"
  "personal correspondence corpus; prior DASHI source material"
  "source:john-brown-family-correspondence"
  personalCorrespondence
  true
  false
  false
  "first-person/family evidence carrier only; downstream clinical/causal claims remain separately typed"

aliceFamilyContext : AttributedSource
aliceFamilyContext = attributed-source
  "Alice Brown"
  "family-context references in prior correspondence corpus"
  "personal/family source corpus; prior DASHI material"
  "source:alice-brown-family-context"
  familyTestimony
  false
  false
  false
  "relational/context coordinate only; does not manufacture attributed beliefs, diagnoses, or events"

------------------------------------------------------------------------
-- HYPERFABRIC AXES
------------------------------------------------------------------------

data TraumaMemoryLearningAxis : Set where
  traumaExposureAxis : TraumaMemoryLearningAxis
  rememberedContentAxis : TraumaMemoryLearningAxis
  memoryConfidenceAxis : TraumaMemoryLearningAxis
  presentTriggerAxis : TraumaMemoryLearningAxis
  learnedResponseAxis : TraumaMemoryLearningAxis
  relationalContextAxis : TraumaMemoryLearningAxis
  protectiveAttachmentAxis : TraumaMemoryLearningAxis
  accessibilityAxis : TraumaMemoryLearningAxis
  communicationSafetyAxis : TraumaMemoryLearningAxis
  provenanceAxis : TraumaMemoryLearningAxis

record SituatedTraumaMemoryLearningState : Set where
  constructor situated-tml-state
  field
    traumaExposure : Bool
    rememberedContentPresent : Bool
    memoryConfidenceHigh : Bool
    presentTrigger : Bool
    learnedResponseAvailable : Bool
    relationalSupportAvailable : Bool
    protectiveAttachmentAvailable : Bool
    protectiveAttachmentAccessibleNow : Bool
    safeToPublishAsProtectiveNarrative : Bool
    provenancePaid : Bool
open SituatedTraumaMemoryLearningState public

------------------------------------------------------------------------
-- FACTORSTHROUGH: MEMORY CONTENT != CURRENT RESPONSE / ACCESSIBILITY
------------------------------------------------------------------------

data SameMemorySurfaceState : Set where
  sameMemoryNoLearnedResource : SameMemorySurfaceState
  sameMemoryWithLearnedResource : SameMemorySurfaceState

data MemoryOnlySurface : Set where
  sameRememberedContent : MemoryOnlySurface

memoryOnlyObserver : SameMemorySurfaceState → MemoryOnlySurface
memoryOnlyObserver sameMemoryNoLearnedResource = sameRememberedContent
memoryOnlyObserver sameMemoryWithLearnedResource = sameRememberedContent

learnedResourceConsumer : SameMemorySurfaceState → Bool
learnedResourceConsumer sameMemoryNoLearnedResource = false
learnedResourceConsumer sameMemoryWithLearnedResource = true

learnedResourceDiffers :
  learnedResourceConsumer sameMemoryNoLearnedResource ≡
  learnedResourceConsumer sameMemoryWithLearnedResource → ⊥
learnedResourceDiffers ()

memoryOnlyNonFactorability :
  INF.NonFactorabilityWitness memoryOnlyObserver learnedResourceConsumer
memoryOnlyNonFactorability = INF.nonFactorabilityWitness
  sameMemoryNoLearnedResource
  sameMemoryWithLearnedResource
  refl
  learnedResourceDiffers

memoryContentCannotDetermineLearnedResource :
  INF.FactorsThrough memoryOnlyObserver learnedResourceConsumer → ⊥
memoryContentCannotDetermineLearnedResource =
  INF.witnessRulesOutEveryFlatFactorisation memoryOnlyNonFactorability

------------------------------------------------------------------------
-- INTERSECTIONALITY: SAME TRAUMA LABEL, DIFFERENT SITUATED ACCESS
------------------------------------------------------------------------

data SameTraumaLabelState : Set where
  sameTraumaLabelSupportUnavailable : SameTraumaLabelState
  sameTraumaLabelSupportAccessible : SameTraumaLabelState

data TraumaLabelSurface : Set where
  sameTraumaLabel : TraumaLabelSurface

traumaLabelObserver : SameTraumaLabelState → TraumaLabelSurface
traumaLabelObserver sameTraumaLabelSupportUnavailable = sameTraumaLabel
traumaLabelObserver sameTraumaLabelSupportAccessible = sameTraumaLabel

supportAccessibilityConsumer : SameTraumaLabelState → Bool
supportAccessibilityConsumer sameTraumaLabelSupportUnavailable = false
supportAccessibilityConsumer sameTraumaLabelSupportAccessible = true

supportAccessibilityDiffers :
  supportAccessibilityConsumer sameTraumaLabelSupportUnavailable ≡
  supportAccessibilityConsumer sameTraumaLabelSupportAccessible → ⊥
supportAccessibilityDiffers ()

traumaLabelNonFactorability :
  INF.NonFactorabilityWitness traumaLabelObserver supportAccessibilityConsumer
traumaLabelNonFactorability = INF.nonFactorabilityWitness
  sameTraumaLabelSupportUnavailable
  sameTraumaLabelSupportAccessible
  refl
  supportAccessibilityDiffers

traumaLabelCannotDetermineSituatedSupport :
  INF.FactorsThrough traumaLabelObserver supportAccessibilityConsumer → ⊥
traumaLabelCannotDetermineSituatedSupport =
  INF.witnessRulesOutEveryFlatFactorisation traumaLabelNonFactorability

------------------------------------------------------------------------
-- WRONGTYPE: SOURCE ROLE / CLAIM ROLE / CONSUMER ROLE
------------------------------------------------------------------------

data PersonalTestimonyImpliesClinicalDiagnosis : Set where
data RememberedContentImpliesHistoricalAccuracy : Set where
data FamilyContextImpliesOtherPersonsMentalState : Set where
data SocialMediaAccountImpliesPrimaryStudyAuthority : Set where
data ProtectiveFactorImpliesGuaranteedOutcome : Set where

testimonyDoesNotManufactureDiagnosis : PersonalTestimonyImpliesClinicalDiagnosis → ⊥
testimonyDoesNotManufactureDiagnosis ()

memoryReportDoesNotManufactureHistoricalAccuracy :
  RememberedContentImpliesHistoricalAccuracy → ⊥
memoryReportDoesNotManufactureHistoricalAccuracy ()

familyContextDoesNotManufactureAnotherMentalState :
  FamilyContextImpliesOtherPersonsMentalState → ⊥
familyContextDoesNotManufactureAnotherMentalState ()

instagramDoesNotBecomePrimaryStudyAuthority :
  SocialMediaAccountImpliesPrimaryStudyAuthority → ⊥
instagramDoesNotBecomePrimaryStudyAuthority ()

protectiveFactorDoesNotGuaranteeOutcome : ProtectiveFactorImpliesGuaranteedOutcome → ⊥
protectiveFactorDoesNotGuaranteeOutcome ()

------------------------------------------------------------------------
-- ADMISSIBILITY: LEARNING / COMMUNICATION TRANSITIONS ARE SITUATED
------------------------------------------------------------------------

data LearningState : Set where
  unsupportedState : LearningState
  supportedState : LearningState

data LearningMove : Set where
  rehearseProtectiveResource : LearningMove

data LearningParameter : Set where
  currentContext : LearningParameter

LearningEnabled : LearningMove → LearningParameter → LearningState → Set
LearningEnabled rehearseProtectiveResource currentContext unsupportedState = ⊥
LearningEnabled rehearseProtectiveResource currentContext supportedState = ⊤

learningStep : LearningMove → LearningParameter → LearningState → LearningState
learningStep rehearseProtectiveResource currentContext unsupportedState = unsupportedState
learningStep rehearseProtectiveResource currentContext supportedState = supportedState

LearningInvariant : LearningState → Set
LearningInvariant unsupportedState = ⊤
LearningInvariant supportedState = ⊤

learningPreserves :
  (move : LearningMove) (parameter : LearningParameter) (state : LearningState) →
  LearningEnabled move parameter state →
  LearningInvariant state →
  LearningInvariant (learningStep move parameter state)
learningPreserves rehearseProtectiveResource currentContext unsupportedState ()
learningPreserves rehearseProtectiveResource currentContext supportedState enabled invariant = tt

traumaMemoryLearningTransitionSystem : Admissible.AdmissibleTransitionSystem
traumaMemoryLearningTransitionSystem = Admissible.admissibleTransitionSystem
  LearningState
  LearningParameter
  LearningMove
  LearningEnabled
  learningStep
  LearningInvariant
  learningPreserves
  "trauma-memory-learning: situated protective-resource rehearsal"

------------------------------------------------------------------------
-- APPEND-ONLY / SNOWBALL PAYMENT BOUNDARIES
------------------------------------------------------------------------

data LaterEvidenceRewritesEarlierSource : Set where
data LaterEvidencePaysEarlierIdentityAutomatically : Set where
data AcquisitionOrderEqualsPaymentOrder : Set where

evidenceAppendOnly : LaterEvidenceRewritesEarlierSource → ⊥
evidenceAppendOnly ()

laterEvidenceDoesNotAutoPayEarlierIdentity :
  LaterEvidencePaysEarlierIdentityAutomatically → ⊥
laterEvidenceDoesNotAutoPayEarlierIdentity ()

acquisitionOrderNeedNotEqualPaymentOrder : AcquisitionOrderEqualsPaymentOrder → ⊥
acquisitionOrderNeedNotEqualPaymentOrder ()

record TraumaMemoryLearningBoundary : Set where
  constructor trauma-memory-learning-boundary
  field
    riskAndProtectiveConsumersDistinct : Bool
    memoryAndHistoricalAccuracyDistinct : Bool
    traumaLabelAndSituatedAccessDistinct : Bool
    testimonyAndDiagnosisDistinct : Bool
    socialMediaAndPrimaryStudyAuthorityDistinct : Bool
    learningTransitionsRequireSituatedEnablement : Bool
    evidenceAppendOnlyIsRequired : Bool
    acquisitionMayBeOutOfPaymentOrder : Bool
open TraumaMemoryLearningBoundary public

canonicalTraumaMemoryLearningBoundary : TraumaMemoryLearningBoundary
canonicalTraumaMemoryLearningBoundary = trauma-memory-learning-boundary
  true true true true true true true true
