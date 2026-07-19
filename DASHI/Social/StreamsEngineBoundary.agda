module DASHI.Social.StreamsEngineBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)

import DASHI.Core.CandidateOnlyCore as CandidateOnly
import DASHI.Core.GenericReceipt as GenericReceipt

------------------------------------------------------------------------
-- Candidate-only Streams Engine boundary.
--
-- This module formalises the shared time-series carrier discussed for the
-- TiRC/SensibLaw stack without promoting analytic, legal, clinical, trading,
-- diagnostic, or evidentiary authority.
--
-- The fixed architecture is:
--   layer 0  text and concept substrate
--   layer 1  events and actors
--   layer 2  claims and cases
--   layer 3  normative systems and sources
--   layer 4  wrong types and duties
--   layer 5  protected interests and harms
--   layer 6  value frames and remedies
--
-- Finance, conversation, and legal-pressure streams are first-class peers.
-- A stream point is derived and must retain provenance to contributing source
-- anchors.  Cross-stream pattern detection may emit a candidate event, but it
-- cannot itself discharge a WrongType, diagnosis, legal finding, trading
-- conclusion, or moral verdict.

listCount : ∀ {A : Set} → List A → Nat
listCount [] = zero
listCount (_ ∷ xs) = suc (listCount xs)

data Never : Set where

------------------------------------------------------------------------
-- Fixed layer vocabulary.

data OntologyLayer : Set where
  textConceptSubstrateLayer : OntologyLayer
  eventsActorsLayer : OntologyLayer
  claimsCasesLayer : OntologyLayer
  normativeSystemsSourcesLayer : OntologyLayer
  wrongTypesDutiesLayer : OntologyLayer
  protectedInterestsHarmsLayer : OntologyLayer
  valueFramesRemediesLayer : OntologyLayer

canonicalOntologyLayers : List OntologyLayer
canonicalOntologyLayers =
  textConceptSubstrateLayer
  ∷ eventsActorsLayer
  ∷ claimsCasesLayer
  ∷ normativeSystemsSourcesLayer
  ∷ wrongTypesDutiesLayer
  ∷ protectedInterestsHarmsLayer
  ∷ valueFramesRemediesLayer
  ∷ []

canonicalOntologyLayerCount : Nat
canonicalOntologyLayerCount = listCount canonicalOntologyLayers

------------------------------------------------------------------------
-- First-class stream vocabulary.

data StreamFamily : Set where
  financeStreamFamily : StreamFamily
  conversationStreamFamily : StreamFamily
  socialFeedStreamFamily : StreamFamily
  legalPressureStreamFamily : StreamFamily
  obligationStreamFamily : StreamFamily
  eventDensityStreamFamily : StreamFamily
  userDefinedStreamFamily : String → StreamFamily

data StreamMeasure : Set where
  monetaryFlowMeasure : StreamMeasure
  accountBalanceMeasure : StreamMeasure
  dependencyRatioMeasure : StreamMeasure
  sentimentMeasure : StreamMeasure
  concernMeasure : StreamMeasure
  controlLanguageMeasure : StreamMeasure
  blameLanguageMeasure : StreamMeasure
  empathyMeasure : StreamMeasure
  messageIntensityMeasure : StreamMeasure
  obligationCountMeasure : StreamMeasure
  legalPressureMeasure : StreamMeasure
  eventCountMeasure : StreamMeasure
  namedMeasure : String → StreamMeasure

data StreamDirection : Set where
  actorAToActorB : StreamDirection
  actorBToActorA : StreamDirection
  jointDirection : StreamDirection
  systemicDirection : StreamDirection
  directionNotApplicable : StreamDirection

data StreamUnit : Set where
  minorCurrencyUnit : StreamUnit
  ratioUnit : StreamUnit
  boundedScoreUnit : StreamUnit
  countUnit : StreamUnit
  durationUnit : StreamUnit
  namedUnit : String → StreamUnit

data StreamDerivationKind : Set where
  rawObservationDerivation : StreamDerivationKind
  deterministicRuleDerivation : StreamDerivationKind
  statisticalAggregationDerivation : StreamDerivationKind
  modelSuggestionDerivation : StreamDerivationKind
  userAssertionDerivation : StreamDerivationKind
  externallyAdjudicatedDerivation : StreamDerivationKind

------------------------------------------------------------------------
-- Provenance anchors remain typed rather than hidden in an opaque payload.

data SourceAnchorKind : Set where
  textBlockAnchor : SourceAnchorKind
  documentAnchor : SourceAnchorKind
  sentenceAnchor : SourceAnchorKind
  tokenSpanAnchor : SourceAnchorKind
  utteranceAnchor : SourceAnchorKind
  eventAnchor : SourceAnchorKind
  transactionAnchor : SourceAnchorKind
  transferAnchor : SourceAnchorKind
  provisionAnchor : SourceAnchorKind
  claimAnchor : SourceAnchorKind
  caseAnchor : SourceAnchorKind
  evidenceItemAnchor : SourceAnchorKind
  receiptAnchor : SourceAnchorKind
  namedAnchor : String → SourceAnchorKind

record SourceAnchor : Set where
  constructor sourceAnchor
  field
    anchorKind : SourceAnchorKind
    anchorIdentifier : String
    anchorValidTime : String
    anchorObservedTime : String
    anchorSourceLabel : String

record StreamDefinition : Set where
  constructor streamDefinition
  field
    streamIdentifier : String
    streamLabel : String
    streamFamily : StreamFamily
    streamMeasure : StreamMeasure
    streamDirection : StreamDirection
    streamUnit : StreamUnit
    subjectActorIdentifier : String
    relationshipIdentifier : String
    derivationKind : StreamDerivationKind
    definitionReading : String

record StreamPoint : Set where
  constructor streamPoint
  field
    pointStream : StreamDefinition
    pointTime : String
    pointValueNumerator : Nat
    pointValueDenominator : Nat
    pointProvenance : List SourceAnchor
    pointExplanation : String

------------------------------------------------------------------------
-- A stored point is admissible only when it retains at least one source
-- anchor.  This is deliberately weaker than proof of truth or causation.

data NonEmpty {A : Set} : List A → Set where
  one : ∀ {x xs} → NonEmpty (x ∷ xs)

record AdmissibleStreamPoint (point : StreamPoint) : Set where
  constructor admissibleStreamPoint
  field
    provenancePresent : NonEmpty (StreamPoint.pointProvenance point)

------------------------------------------------------------------------
-- Cross-stream pattern surfaces.

data PatternKind : Set where
  thresholdCrossingPattern : PatternKind
  rollingShiftPattern : PatternKind
  clusteredChangePointPattern : PatternKind
  relationalShiftPattern : PatternKind
  financialShockClusterPattern : PatternKind
  financeConversationAlignmentPattern : PatternKind
  legalPressureAlignmentPattern : PatternKind
  namedPattern : String → PatternKind

data InterpretationStatus : Set where
  measuredSignalStatus : InterpretationStatus
  derivedSignalStatus : InterpretationStatus
  candidatePatternStatus : InterpretationStatus
  userConfirmedPatternStatus : InterpretationStatus
  externallyReviewedPatternStatus : InterpretationStatus
  adjudicatedFindingStatus : InterpretationStatus

data PatternRoute : Set where
  candidateEventRoute : PatternRoute
  reviewQueueRoute : PatternRoute
  userAnnotationRoute : PatternRoute
  legalFindingPromotionRoute : PatternRoute
  clinicalDiagnosisPromotionRoute : PatternRoute
  tradingAuthorityPromotionRoute : PatternRoute
  moralVerdictPromotionRoute : PatternRoute
  causalProofPromotionRoute : PatternRoute

AdmissiblePatternRoute : PatternRoute → Set
AdmissiblePatternRoute candidateEventRoute = ⊤
AdmissiblePatternRoute reviewQueueRoute = ⊤
AdmissiblePatternRoute userAnnotationRoute = ⊤
AdmissiblePatternRoute legalFindingPromotionRoute = Never
AdmissiblePatternRoute clinicalDiagnosisPromotionRoute = Never
AdmissiblePatternRoute tradingAuthorityPromotionRoute = Never
AdmissiblePatternRoute moralVerdictPromotionRoute = Never
AdmissiblePatternRoute causalProofPromotionRoute = Never

legalFindingPromotionRejected :
  AdmissiblePatternRoute legalFindingPromotionRoute → Never
legalFindingPromotionRejected impossible = impossible

clinicalDiagnosisPromotionRejected :
  AdmissiblePatternRoute clinicalDiagnosisPromotionRoute → Never
clinicalDiagnosisPromotionRejected impossible = impossible

tradingAuthorityPromotionRejected :
  AdmissiblePatternRoute tradingAuthorityPromotionRoute → Never
tradingAuthorityPromotionRejected impossible = impossible

moralVerdictPromotionRejected :
  AdmissiblePatternRoute moralVerdictPromotionRoute → Never
moralVerdictPromotionRejected impossible = impossible

causalProofPromotionRejected :
  AdmissiblePatternRoute causalProofPromotionRoute → Never
causalProofPromotionRejected impossible = impossible

record StreamPattern : Set where
  constructor streamPattern
  field
    patternIdentifier : String
    patternKind : PatternKind
    patternStatus : InterpretationStatus
    patternWindowStart : String
    patternWindowEnd : String
    patternStreams : List StreamDefinition
    patternProvenance : List SourceAnchor
    patternSummary : String
    patternLimitations : String

record AdmissibleStreamPattern (pattern : StreamPattern) : Set where
  constructor admissibleStreamPattern
  field
    streamEvidencePresent : NonEmpty (StreamPattern.patternStreams pattern)
    patternProvenancePresent : NonEmpty (StreamPattern.patternProvenance pattern)
    candidateOnlyStatus :
      StreamPattern.patternStatus pattern ≡ candidatePatternStatus

------------------------------------------------------------------------
-- Two-way integration boundary.
--
-- Upward: source events, transactions, utterances, provisions, and claims can
-- be aggregated into stream points and candidate patterns.
-- Downward: reviewed pattern surfaces may create candidate Event/Claim links
-- or review annotations.  They do not mutate raw source records and do not
-- promote findings merely because the visualisation displays alignment.

data FeedbackKind : Set where
  sourceToStreamAggregation : FeedbackKind
  streamToCandidateEvent : FeedbackKind
  streamToReviewAnnotation : FeedbackKind
  userCorrectionToDerivation : FeedbackKind
  ontologyRevisionToClassifier : FeedbackKind
  classifierGapToOntologyReview : FeedbackKind

record BidirectionalStreamLink : Set where
  constructor bidirectionalStreamLink
  field
    feedbackKind : FeedbackKind
    sourceAnchor : SourceAnchor
    targetIdentifier : String
    preservesRawSource : Bool
    preservesRawSourceIsTrue : preservesRawSource ≡ true
    isReviewable : Bool
    isReviewableIsTrue : isReviewable ≡ true
    linkReading : String

------------------------------------------------------------------------
-- Neutral naming and interpretation governance.

data NamingPolicy : Set where
  structuralNeutralNaming : NamingPolicy
  genderNeutralDefaultNaming : NamingPolicy
  nonPathologisingNaming : NamingPolicy
  perspectiveExplicitMoralEvaluation : NamingPolicy
  rawEvidencePreservingNaming : NamingPolicy

data AuthorityClaim : Set where
  visualizationClaim : AuthorityClaim
  aggregationClaim : AuthorityClaim
  candidatePatternClaim : AuthorityClaim
  legalAuthorityClaim : AuthorityClaim
  clinicalAuthorityClaim : AuthorityClaim
  tradingAuthorityClaim : AuthorityClaim
  causalAuthorityClaim : AuthorityClaim
  moralTruthAuthorityClaim : AuthorityClaim

AuthorityBlocked : AuthorityClaim → Bool
AuthorityBlocked visualizationClaim = false
AuthorityBlocked aggregationClaim = false
AuthorityBlocked candidatePatternClaim = false
AuthorityBlocked legalAuthorityClaim = true
AuthorityBlocked clinicalAuthorityClaim = true
AuthorityBlocked tradingAuthorityClaim = true
AuthorityBlocked causalAuthorityClaim = true
AuthorityBlocked moralTruthAuthorityClaim = true

------------------------------------------------------------------------
-- Canonical receipt surfaces.

canonicalStreamsEngineCandidateRow : CandidateOnly.CandidateOnlyRow
canonicalStreamsEngineCandidateRow =
  CandidateOnly.mkCandidateOnlyRow
    "streams engine candidate"
    "DASHI.Social.StreamsEngineBoundary"
    "canonicalStreamsEngineCandidateRow"
    CandidateOnly.diagnosticCandidateKind
    CandidateOnly.diagnosticCandidateOnlyStatus
    "finance, conversation, social-feed, legal-pressure, obligation, and event-density streams share one provenance-preserving time-series carrier"
    "stream alignment and change detection remain candidate-only; they do not establish abuse, causation, diagnosis, legal liability, trading advice, moral truth, or evidentiary admissibility"

canonicalStreamsEngineCandidateReceipt :
  CandidateOnly.CandidateOnlyReceipt canonicalStreamsEngineCandidateRow
canonicalStreamsEngineCandidateReceipt =
  CandidateOnly.canonicalCandidateOnlyReceipt
    canonicalStreamsEngineCandidateRow
    refl refl refl refl refl refl refl refl

canonicalStreamsEngineReceipt : GenericReceipt.GenericReceipt
canonicalStreamsEngineReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "streams engine boundary"
    "DASHI.Social.StreamsEngineBoundary"
    "canonicalStreamsEngineSurface"
    "first-class finance, conversation, social-feed, legal-pressure, obligation, and event-density streams are represented as derived time-series with typed provenance and bidirectional review links"
    "derived signals and candidate patterns do not promote legal, clinical, trading, causal, evidentiary, governance, or moral authority"
    "agda -i . DASHI/Social/StreamsEngineBoundary.agda"
