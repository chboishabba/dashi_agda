module DASHI.Law.SensibLawAnonymisedLivedHistoryHyperformalIntakeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.SnowballAtomWrongTypeScaleInvariantExact as Atom
import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.AdmissibleTransitionHyperfabricExact as Admissible

------------------------------------------------------------------------
-- ANONYMISED LIVED-HISTORY INTAKE / HYPERFORMAL UI OWNER
--
-- This is deliberately NOT a private-person case file.  It formalises the
-- reusable grammar needed when a person brings a large, non-linear history to
-- a professional consumer (legal, clinical, referral, document-support, etc.).
--
-- The specimen is anonymised by construction:
--   * no real names, addresses, institutions, dates, diagnoses or allegations;
--   * display identities are role aliases only;
--   * source pointers may exist out-of-band but are not embedded here;
--   * source presence, remembered content, historical truth, legal relevance,
--     clinical interpretation and downstream causation remain distinct.
--
-- Cross-pollinated only through repo-native machinery:
--   Atom / WrongType / Snowball payment
--   Intersectional FactorsThrough / non-factorability
--   Admissible transition hyperfabric
------------------------------------------------------------------------

------------------------------------------------------------------------
-- SOURCE / EVENT GRAIN
------------------------------------------------------------------------

data DisplayRole : Set where
  personA : DisplayRole
  professionalB : DisplayRole
  institutionC : DisplayRole
  thirdPartyD : DisplayRole

data HistoryAtom : Set where
  firstPersonReport : HistoryAtom
  contemporaneousRecording : HistoryAtom
  contemporaneousDocument : HistoryAtom
  thirdPartyReport : HistoryAtom
  institutionalRecord : HistoryAtom
  derivedSynthesis : HistoryAtom

data ChronologyState : Set where
  exactChronology : ChronologyState
  boundedChronology : ChronologyState
  approximateChronology : ChronologyState
  chronologyUnresolved : ChronologyState

data SourceRoleState : Set where
  sourceReportsEvent : SourceRoleState
  sourceDirectlyRecordsOccurrence : SourceRoleState
  sourceReportsAnotherSource : SourceRoleState
  derivedInterpretationOnly : SourceRoleState

data ConsumerIntent : Set where
  preserveStory : ConsumerIntent
  legalIntake : ConsumerIntent
  clinicalHandoff : ConsumerIntent
  referralBrief : ConsumerIntent
  documentSupport : ConsumerIntent

data IntakeQuery : Set where
  whatHappened : IntakeQuery
  whatCanBeEstablished : IntakeQuery
  whatRuleMakesItMatter : IntakeQuery
  whatIsMissing : IntakeQuery
  whatNext : IntakeQuery

historyAtomGrain : Atom.AtomGrain ConsumerIntent IntakeQuery
historyAtomGrain = Atom.atom-grain
  HistoryAtom
  legalIntake
  whatCanBeEstablished
  (λ _ → Atom.sourceProposition)
  (λ _ → true)
  (λ _ → true)

------------------------------------------------------------------------
-- WRONGTYPE: A VALID OBJECT MAY STILL BE THE WRONG OBJECT FOR THIS CONSUMER.
------------------------------------------------------------------------

data IntakeClassification : Set where
  reportedOnly : IntakeClassification
  artefactBearing : IntakeClassification
  institutionBearing : IntakeClassification
  derivedOnly : IntakeClassification

classifyHistoryAtom : HistoryAtom → IntakeClassification
classifyHistoryAtom firstPersonReport = reportedOnly
classifyHistoryAtom contemporaneousRecording = artefactBearing
classifyHistoryAtom contemporaneousDocument = artefactBearing
classifyHistoryAtom thirdPartyReport = reportedOnly
classifyHistoryAtom institutionalRecord = institutionBearing
classifyHistoryAtom derivedSynthesis = derivedOnly

historyWrongTypeFamily : Atom.WrongTypeFamily HistoryAtom IntakeClassification
historyWrongTypeFamily = Atom.wrong-type-family
  classifyHistoryAtom
  true
  true
  false

data RecollectionAutomaticallyEstablishesOccurrence : Set where
data RecordingAutomaticallyEstablishesLegalCharacterisation : Set where
data InstitutionalRecordAutomaticallyEstablishesIndependentTruth : Set where
data DerivedSummaryAutomaticallyReplacesUnderlyingHistory : Set where

recollectionDoesNotAutoEstablishOccurrence :
  RecollectionAutomaticallyEstablishesOccurrence → ⊥
recollectionDoesNotAutoEstablishOccurrence ()

recordingDoesNotAutoEstablishLegalCharacterisation :
  RecordingAutomaticallyEstablishesLegalCharacterisation → ⊥
recordingDoesNotAutoEstablishLegalCharacterisation ()

institutionalRecordDoesNotAutoEstablishIndependentTruth :
  InstitutionalRecordAutomaticallyEstablishesIndependentTruth → ⊥
institutionalRecordDoesNotAutoEstablishIndependentTruth ()

derivedSummaryDoesNotReplaceUnderlyingHistory :
  DerivedSummaryAutomaticallyReplacesUnderlyingHistory → ⊥
derivedSummaryDoesNotReplaceUnderlyingHistory ()

------------------------------------------------------------------------
-- SNOWBALL: ACQUISITION MAY BE BROAD; PAYMENT REMAINS CONSUMER-RELATIVE.
------------------------------------------------------------------------

data IntakePaymentReceipt : Set where
  directRecordingReceipt : IntakePaymentReceipt
  directDocumentReceipt : IntakePaymentReceipt

acquiredHistoryAtom : HistoryAtom → Bool
acquiredHistoryAtom firstPersonReport = true
acquiredHistoryAtom contemporaneousRecording = true
acquiredHistoryAtom contemporaneousDocument = true
acquiredHistoryAtom thirdPartyReport = true
acquiredHistoryAtom institutionalRecord = true
acquiredHistoryAtom derivedSynthesis = true

paidHistoryAtom : HistoryAtom → Bool
paidHistoryAtom firstPersonReport = false
paidHistoryAtom contemporaneousRecording = true
paidHistoryAtom contemporaneousDocument = true
paidHistoryAtom thirdPartyReport = false
paidHistoryAtom institutionalRecord = false
paidHistoryAtom derivedSynthesis = false

receiptHistoryAtom : IntakePaymentReceipt → HistoryAtom
receiptHistoryAtom directRecordingReceipt = contemporaneousRecording
receiptHistoryAtom directDocumentReceipt = contemporaneousDocument

receiptPaysHistoryAtom :
  (receipt : IntakePaymentReceipt) →
  paidHistoryAtom (receiptHistoryAtom receipt) ≡ true
receiptPaysHistoryAtom directRecordingReceipt = refl
receiptPaysHistoryAtom directDocumentReceipt = refl

historySnowballInvariant :
  Atom.SnowballAcquisitionPaymentInvariant HistoryAtom IntakePaymentReceipt
historySnowballInvariant = Atom.snowball-acquisition-payment-invariant
  acquiredHistoryAtom
  paidHistoryAtom
  receiptHistoryAtom
  receiptPaysHistoryAtom
  true
  false
  false
  true
  true

------------------------------------------------------------------------
-- CONSUMER PROJECTION: A SMALL CASE VIEW MAY ANSWER ONE QUESTION WITHOUT
-- BEING A SUFFICIENT REPRESENTATION OF THE PERSON'S FULL HISTORY.
------------------------------------------------------------------------

data SituatedHistoryState : Set where
  sameCaseSliceOneThread : SituatedHistoryState
  sameCaseSliceManyThreads : SituatedHistoryState

data SmallCaseSurface : Set where
  currentIssueSupported : SmallCaseSurface

data CurrentProfessionalAnswer : Set where
  boundedQuestionReady : CurrentProfessionalAnswer

data StoryContinuityOutcome : Set where
  oneThreadVisible : StoryContinuityOutcome
  manyThreadsRetained : StoryContinuityOutcome

smallCaseProjection : SituatedHistoryState → SmallCaseSurface
smallCaseProjection sameCaseSliceOneThread = currentIssueSupported
smallCaseProjection sameCaseSliceManyThreads = currentIssueSupported

currentProfessionalConsumer : SituatedHistoryState → CurrentProfessionalAnswer
currentProfessionalConsumer sameCaseSliceOneThread = boundedQuestionReady
currentProfessionalConsumer sameCaseSliceManyThreads = boundedQuestionReady

interpretSmallCase : SmallCaseSurface → CurrentProfessionalAnswer
interpretSmallCase currentIssueSupported = boundedQuestionReady

smallCaseFactorsForCurrentProfessionalQuestion :
  INF.FactorsThrough smallCaseProjection currentProfessionalConsumer
smallCaseFactorsForCurrentProfessionalQuestion = INF.factorsThrough
  interpretSmallCase
  (λ { sameCaseSliceOneThread → refl ; sameCaseSliceManyThreads → refl })

storyContinuityConsumer : SituatedHistoryState → StoryContinuityOutcome
storyContinuityConsumer sameCaseSliceOneThread = oneThreadVisible
storyContinuityConsumer sameCaseSliceManyThreads = manyThreadsRetained

storyContinuityDiffers :
  storyContinuityConsumer sameCaseSliceOneThread ≡
  storyContinuityConsumer sameCaseSliceManyThreads → ⊥
storyContinuityDiffers ()

smallCaseCannotRecoverWholeStoryWitness :
  INF.NonFactorabilityWitness smallCaseProjection storyContinuityConsumer
smallCaseCannotRecoverWholeStoryWitness = INF.nonFactorabilityWitness
  sameCaseSliceOneThread
  sameCaseSliceManyThreads
  refl
  storyContinuityDiffers

smallCaseCannotReplaceWholeStory :
  INF.FactorsThrough smallCaseProjection storyContinuityConsumer → ⊥
smallCaseCannotReplaceWholeStory =
  INF.witnessRulesOutEveryFlatFactorisation smallCaseCannotRecoverWholeStoryWitness

------------------------------------------------------------------------
-- STORY VIEW / CASE VIEW BOUNDARY.
------------------------------------------------------------------------

record ConsumerProjectionBoundary : Set where
  constructor consumer-projection-boundary
  field
    consumer : ConsumerIntent
    showsWholeHistoryByDefault : Bool
    sourceReopenable : Bool
    omittedFromProjectionMeansDeleted : Bool
    projectionCreatesTruth : Bool
    projectionCreatesLegalAdvice : Bool
open ConsumerProjectionBoundary public

legalIntakeProjectionBoundary : ConsumerProjectionBoundary
legalIntakeProjectionBoundary = consumer-projection-boundary
  legalIntake false true false false false

storyProjectionBoundary : ConsumerProjectionBoundary
storyProjectionBoundary = consumer-projection-boundary
  preserveStory true true false false false

------------------------------------------------------------------------
-- NON-LINEAR MEMORY CAPTURE AS AN ADMISSIBLE BRANCH-AND-RETURN FIBRE.
--
-- A side memory is not forced into the active chronology before it can be
-- retained.  Capturing it preserves a return anchor to the previous thread.
------------------------------------------------------------------------

data CaptureState : Set where
  mainThreadAnchored : CaptureState
  sideThreadOpen : CaptureState
  sideThreadStored : CaptureState

data CaptureParameter : Set where
  currentSession : CaptureParameter

data CaptureMove : Set where
  forkTriggeredMemory : CaptureMove
  storeSideThread : CaptureMove
  returnToPriorThread : CaptureMove

CaptureEnabled : CaptureMove → CaptureParameter → CaptureState → Set
CaptureEnabled forkTriggeredMemory currentSession mainThreadAnchored = ⊤
CaptureEnabled forkTriggeredMemory currentSession sideThreadOpen = ⊥
CaptureEnabled forkTriggeredMemory currentSession sideThreadStored = ⊥
CaptureEnabled storeSideThread currentSession mainThreadAnchored = ⊥
CaptureEnabled storeSideThread currentSession sideThreadOpen = ⊤
CaptureEnabled storeSideThread currentSession sideThreadStored = ⊥
CaptureEnabled returnToPriorThread currentSession mainThreadAnchored = ⊥
CaptureEnabled returnToPriorThread currentSession sideThreadOpen = ⊥
CaptureEnabled returnToPriorThread currentSession sideThreadStored = ⊤

captureStep : CaptureMove → CaptureParameter → CaptureState → CaptureState
captureStep forkTriggeredMemory currentSession mainThreadAnchored = sideThreadOpen
captureStep forkTriggeredMemory currentSession sideThreadOpen = sideThreadOpen
captureStep forkTriggeredMemory currentSession sideThreadStored = sideThreadStored
captureStep storeSideThread currentSession mainThreadAnchored = mainThreadAnchored
captureStep storeSideThread currentSession sideThreadOpen = sideThreadStored
captureStep storeSideThread currentSession sideThreadStored = sideThreadStored
captureStep returnToPriorThread currentSession mainThreadAnchored = mainThreadAnchored
captureStep returnToPriorThread currentSession sideThreadOpen = sideThreadOpen
captureStep returnToPriorThread currentSession sideThreadStored = mainThreadAnchored

CaptureInvariant : CaptureState → Set
CaptureInvariant _ = ⊤

capturePreserves :
  (move : CaptureMove) (parameter : CaptureParameter) (state : CaptureState) →
  CaptureEnabled move parameter state →
  CaptureInvariant state →
  CaptureInvariant (captureStep move parameter state)
capturePreserves move parameter state enabled invariant = tt

livedHistoryCaptureTransitionSystem : Admissible.AdmissibleTransitionSystem
livedHistoryCaptureTransitionSystem = Admissible.admissibleTransitionSystem
  CaptureState
  CaptureParameter
  CaptureMove
  CaptureEnabled
  captureStep
  CaptureInvariant
  capturePreserves
  "sensiblaw:lived-history:branch-and-return-capture"

------------------------------------------------------------------------
-- EVIDENCE LADDER: DISPLAY SUPPORT WITHOUT COLLAPSING SOURCE ROLES.
------------------------------------------------------------------------

record EvidenceLadder : Set where
  constructor evidence-ladder
  field
    firstPersonReportPresent : Bool
    directArtefactPresent : Bool
    contemporaneousSourcePresent : Bool
    thirdPartySourcePresent : Bool
    institutionalSourcePresent : Bool
    conflictingMaterialLocated : Bool
    exactChronologyPaid : Bool
    worldTruthPromoted : Bool
open EvidenceLadder public

anonymisedRecordedEventLadder : EvidenceLadder
anonymisedRecordedEventLadder = evidence-ladder
  true true true false false false false false

------------------------------------------------------------------------
-- HYPERFORMAL RIBBON: WIDTH/MASS IS LENS-RELATIVE, NOT A TRUTH SCORE.
------------------------------------------------------------------------

data RibbonLens : Set where
  legalRelevanceLens : RibbonLens
  sourceSupportLens : RibbonLens
  chronologyLens : RibbonLens
  externalityLens : RibbonLens
  residualDebtLens : RibbonLens

data RibbonFlowKind : Set where
  massBearingContribution : RibbonFlowKind
  contextOnlyLink : RibbonFlowKind
  localDefeater : RibbonFlowKind
  residualFlow : RibbonFlowKind

record HyperformalRibbonFlow : Set where
  constructor hyperformal-ribbon-flow
  field
    flowReference : String
    fromReference : String
    toReference : String
    lens : RibbonLens
    flowKind : RibbonFlowKind
    lensMass : Nat
    sourceReopenable : Bool
    createsTruth : Bool
    createsAuthority : Bool
open HyperformalRibbonFlow public

anonymisedRecordingFlow : HyperformalRibbonFlow
anonymisedRecordingFlow = hyperformal-ribbon-flow
  "anon-flow:recording-to-current-issue"
  "anon-source:recording"
  "anon-locus:current-professional-question"
  sourceSupportLens
  (massBearingContribution)
  (suc (suc zero))
  true false false

anonymisedContextFlow : HyperformalRibbonFlow
anonymisedContextFlow = hyperformal-ribbon-flow
  "anon-flow:identity-context"
  "anon-context:external-identity"
  "anon-locus:current-professional-question"
  sourceSupportLens
  contextOnlyLink
  zero
  true false false

------------------------------------------------------------------------
-- LOCAL DEFEAT / FAILURE IS NOT GLOBAL FALSEHOOD.
------------------------------------------------------------------------

data LocalRouteState : Set where
  routeAdmissibleHere : LocalRouteState
  routeBlockedHere : LocalRouteState

data LocalBlockImpliesGlobalFalsehood : Set where

data DefeaterErasesSourceExistence : Set where

data RibbonWidthCreatesTruth : Set where

data ContextLinkCreatesAuthority : Set where

localBlockDoesNotCreateGlobalFalsehood : LocalBlockImpliesGlobalFalsehood → ⊥
localBlockDoesNotCreateGlobalFalsehood ()

defeaterDoesNotEraseSourceExistence : DefeaterErasesSourceExistence → ⊥
defeaterDoesNotEraseSourceExistence ()

ribbonWidthDoesNotCreateTruth : RibbonWidthCreatesTruth → ⊥
ribbonWidthDoesNotCreateTruth ()

contextLinkDoesNotCreateAuthority : ContextLinkCreatesAuthority → ⊥
contextLinkDoesNotCreateAuthority ()

------------------------------------------------------------------------
-- ANONYMISATION / UI BOUNDARY.
------------------------------------------------------------------------

record AnonymisedLivedHistoryBoundary : Set where
  constructor anonymised-lived-history-boundary
  field
    directIdentifiersEmbedded : Bool
    privateSourcePointersMayRemainOutOfBand : Bool
    displayAliasRewritesPrivateSourceIdentity : Bool
    recollectionEqualsHistoricalTruth : Bool
    professionalProjectionDeletesOmittedHistory : Bool
    sideMemoryMustBeChronologicallyPlacedBeforeCapture : Bool
    smallProjectionMayAnswerIndexedConsumer : Bool
    sameSmallProjectionMustAnswerEveryConsumer : Bool
    ribbonMassIsUniversalProofScore : Bool
    nonMassContextMayRemainVisible : Bool
    sourceCanBeReopenedOnDemand : Bool
    derivedViewCreatesProfessionalAdvice : Bool
open AnonymisedLivedHistoryBoundary public

canonicalAnonymisedLivedHistoryBoundary : AnonymisedLivedHistoryBoundary
canonicalAnonymisedLivedHistoryBoundary = anonymised-lived-history-boundary
  false
  true
  false
  false
  false
  false
  true
  false
  false
  true
  true
  false

------------------------------------------------------------------------
-- MINIMAL ANONYMISED FLAGSHIP FIXTURE.
------------------------------------------------------------------------

record AnonymisedIntakeFixture : Set where
  constructor anonymised-intake-fixture
  field
    focalPerson : DisplayRole
    supportingProfessional : DisplayRole
    respondingInstitution : DisplayRole
    currentConsumer : ConsumerIntent
    currentQuery : IntakeQuery
    chronology : ChronologyState
    evidence : EvidenceLadder
    sideThreadCaptureSystem : Admissible.AdmissibleTransitionSystem
    caseProjection : ConsumerProjectionBoundary
    storyProjection : ConsumerProjectionBoundary
    ribbonFlow : HyperformalRibbonFlow
    containsRealWorldIdentifiers : Bool
    containsClinicalDiagnosis : Bool
    containsAdjudicatedFinding : Bool
open AnonymisedIntakeFixture public

canonicalAnonymisedIntakeFixture : AnonymisedIntakeFixture
canonicalAnonymisedIntakeFixture = anonymised-intake-fixture
  personA
  professionalB
  institutionC
  legalIntake
  whatCanBeEstablished
  approximateChronology
  anonymisedRecordedEventLadder
  livedHistoryCaptureTransitionSystem
  legalIntakeProjectionBoundary
  storyProjectionBoundary
  anonymisedRecordingFlow
  false
  false
  false

------------------------------------------------------------------------
-- CROSS-LANE ANCHORS: REUSE, DO NOT REDEFINE.
------------------------------------------------------------------------

atomScaleBoundary : Atom.ScaleTransportBoundary
atomScaleBoundary = Atom.canonicalScaleTransportBoundary

snowballBoundary : Atom.SnowballAcquisitionPaymentBoundary
snowballBoundary = Atom.canonicalSnowballAcquisitionPaymentBoundary

admissibleTransitionBoundary : Admissible.AdmissibleTransitionBoundary
admissibleTransitionBoundary = Admissible.canonicalAdmissibleTransitionBoundary
