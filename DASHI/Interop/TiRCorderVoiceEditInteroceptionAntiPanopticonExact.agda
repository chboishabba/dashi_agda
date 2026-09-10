module DASHI.Interop.TiRCorderVoiceEditInteroceptionAntiPanopticonExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Biology.EmbodiedOptionConeInteroceptionExact as Embodied
import DASHI.Biology.InteroceptiveRefreshCalibrationExact as Refresh
import DASHI.Interop.GodsEyeViewProofCarryingWorldOntologyExact as Anti

------------------------------------------------------------------------
-- TIRCORDER x STATIBAKER x ITIR VOICE-EDIT / INTEROCEPTION BOUNDARY
--
-- Repository implementation coordinates:
--   TiRCorder preserves capture/transcription and can fan transcript artifacts
--   to SensibLaw / StatiBaker.
--   StatiBaker preserves append-only observed signals and explicitly treats
--   drift/metrics as observations rather than diagnosis, scoring or agency.
--
-- This owner formalises the ideal seam.  It does NOT claim that correction
-- frequency diagnoses a body state, neurotype, impairment, intent or clinical
-- condition.  Interoception is a possible user-selected *consumer* of a
-- descriptive metric, not the meaning of the metric itself.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- 1. Verbatim, edit log and rendered document are different carriers.
------------------------------------------------------------------------

record VerbatimTranscriptRef : Set where
  constructor verbatimTranscriptRef
  field
    transcriptId : String
    audioSourceReference : String
    transcriptArtifactReference : String

open VerbatimTranscriptRef public

data VoiceEditKind : Set where
  insertText : VoiceEditKind
  replaceRecent : VoiceEditKind
  deleteRecent : VoiceEditKind
  paragraphBreak : VoiceEditKind
  listify : VoiceEditKind
  punctuate : VoiceEditKind
  formatSelection : VoiceEditKind
  rewriteSelection : VoiceEditKind
  learnCorrection : VoiceEditKind

-- Recognition and interpretation are deliberately separate.  The same spoken
-- token may be ordinary content in one context and an edit command in another.
data SpokenIntentFibre : Set where
  documentContent : SpokenIntentFibre
  selfCorrection : SpokenIntentFibre
  formattingCommand : SpokenIntentFibre
  discourseMarker : SpokenIntentFibre
  quotedSpeech : SpokenIntentFibre
  asrArtifact : SpokenIntentFibre
  unresolvedIntent : SpokenIntentFibre

record VoiceEditEvent : Set where
  constructor voiceEditEvent
  field
    editEventId : String
    occurredAt : String
    sourceTranscript : VerbatimTranscriptRef
    sourceSpanReference : String
    editKind : VoiceEditKind
    intentFibre : SpokenIntentFibre
    argumentReference : String
    replacementReference : String
    interpreterReference : String

open VoiceEditEvent public

record RenderedTranscriptRef : Set where
  constructor renderedTranscriptRef
  field
    renderedId : String
    verbatimSource : VerbatimTranscriptRef
    editLedgerReference : String
    rendererReference : String

open RenderedTranscriptRef public

------------------------------------------------------------------------
-- 2. Admission: unresolved intent is retained, not silently executed.
------------------------------------------------------------------------

data EditExecutionAdmissible : SpokenIntentFibre → Set where
  admitContentInsertion : EditExecutionAdmissible documentContent
  admitSelfCorrection : EditExecutionAdmissible selfCorrection
  admitFormattingCommand : EditExecutionAdmissible formattingCommand

unresolvedIntentCannotExecute : EditExecutionAdmissible unresolvedIntent → ⊥
unresolvedIntentCannotExecute ()

asrArtifactCannotExecuteAsEdit : EditExecutionAdmissible asrArtifact → ⊥
asrArtifactCannotExecuteAsEdit ()

quotedSpeechCannotExecuteAsEdit : EditExecutionAdmissible quotedSpeech → ⊥
quotedSpeechCannotExecuteAsEdit ()

------------------------------------------------------------------------
-- 3. Wrong-consumer firewalls.
--
-- A correctly recognized formatting/correction command routed into document
-- content is a consumer-routing failure, not necessarily an ASR failure.
------------------------------------------------------------------------

data FormattingCommandIsDocumentContent : Set where
formattingCommandIsNotDocumentContent : FormattingCommandIsDocumentContent → ⊥
formattingCommandIsNotDocumentContent ()

data SelfCorrectionIsASRError : Set where
selfCorrectionIsNotNecessarilyASRError : SelfCorrectionIsASRError → ⊥
selfCorrectionIsNotNecessarilyASRError ()

data RenderedTranscriptReplacesVerbatimEvidence : Set where
renderedTranscriptDoesNotReplaceVerbatimEvidence :
  RenderedTranscriptReplacesVerbatimEvidence → ⊥
renderedTranscriptDoesNotReplaceVerbatimEvidence ()

------------------------------------------------------------------------
-- 4. Opt-in metric derivation.
--
-- Configuration and permission are separate.  Merely having correction events
-- does not create permission to derive or export a personal metric.
------------------------------------------------------------------------

record SelfObservationConfig : Set where
  constructor selfObservationConfig
  field
    metricEnabled : Bool
    shareWithStatiBaker : Bool
    windowReference : String
    purposeReference : String

open SelfObservationConfig public

data MetricDerivationAdmissible : SelfObservationConfig → Set where
  explicitMetricOptIn :
    {config : SelfObservationConfig} →
    metricEnabled config ≡ true →
    MetricDerivationAdmissible config

record CorrectionObservation : Set where
  constructor correctionObservation
  field
    observationWindowReference : String
    totalEditEvents : Nat
    selfCorrectionEvents : Nat
    formattingCommandEvents : Nat
    unresolvedIntentEvents : Nat
    derivationReference : String
    declaredPurposeReference : String

open CorrectionObservation public

-- There is intentionally no person-level quality, pathology, competence or
-- diagnosis field in CorrectionObservation.

data StatiBakerMetricExportAdmissible : SelfObservationConfig → Set where
  explicitStatiBakerMetricOptIn :
    {config : SelfObservationConfig} →
    metricEnabled config ≡ true →
    shareWithStatiBaker config ≡ true →
    StatiBakerMetricExportAdmissible config

record StatiBakerCountsOnlyProjection : Set where
  constructor statiBakerCountsOnlyProjection
  field
    sourceObservation : CorrectionObservation
    emittedAt : String
    metricName : String
    eventCount : Nat
    correctionCount : Nat
    formattingCount : Nat
    unresolvedCount : Nat
    projectionReference : String

open StatiBakerCountsOnlyProjection public

------------------------------------------------------------------------
-- 5. Interoceptive use is a consumer projection, not causal interpretation.
------------------------------------------------------------------------

record InteroceptiveReflectionProjection : Set where
  constructor interoceptiveReflectionProjection
  field
    observation : CorrectionObservation
    reflectionWindowReference : String
    userFacingExplanationReference : String
    comparisonBaselineReference : String

open InteroceptiveReflectionProjection public

-- A descriptive speech/edit observation cannot, by itself, determine the body,
-- felt state or diagnosis.  These empty types intentionally block those
-- promotions.
data CorrectionMetricDeterminesBodyState : Set where
correctionMetricDoesNotDetermineBodyState : CorrectionMetricDeterminesBodyState → ⊥
correctionMetricDoesNotDetermineBodyState ()

data CorrectionMetricDeterminesFeltState : Set where
correctionMetricDoesNotDetermineFeltState : CorrectionMetricDeterminesFeltState → ⊥
correctionMetricDoesNotDetermineFeltState ()

data CorrectionMetricCreatesDiagnosis : Set where
correctionMetricDoesNotCreateDiagnosis : CorrectionMetricCreatesDiagnosis → ⊥
correctionMetricDoesNotCreateDiagnosis ()

data CorrectionMetricCreatesCompetenceScore : Set where
correctionMetricDoesNotCreateCompetenceScore : CorrectionMetricCreatesCompetenceScore → ⊥
correctionMetricDoesNotCreateCompetenceScore ()

------------------------------------------------------------------------
-- 6. Anti-panopticon / purpose-limitation boundary.
--
-- Seeing one's own descriptive trend does not confer authority on another
-- consumer.  Export is separately permissioned, observations do not create
-- intervention authority, and visibility is not omniscience.
------------------------------------------------------------------------

data LocalMetricCreatesExternalConsumerAuthority : Set where
localMetricDoesNotCreateExternalConsumerAuthority :
  LocalMetricCreatesExternalConsumerAuthority → ⊥
localMetricDoesNotCreateExternalConsumerAuthority ()

data MetricCreatesSurveillanceAuthority : Set where
metricDoesNotCreateSurveillanceAuthority : MetricCreatesSurveillanceAuthority → ⊥
metricDoesNotCreateSurveillanceAuthority ()

data MetricCreatesDisciplinaryAuthority : Set where
metricDoesNotCreateDisciplinaryAuthority : MetricCreatesDisciplinaryAuthority → ⊥
metricDoesNotCreateDisciplinaryAuthority ()

data DisabledMetricMayAccumulate : Set where
disabledMetricMayNotAccumulate : DisabledMetricMayAccumulate → ⊥
disabledMetricMayNotAccumulate ()

data MetricMayBeSharedByDefault : Set where
metricMayNotBeSharedByDefault : MetricMayBeSharedByDefault → ⊥
metricMayNotBeSharedByDefault ()

------------------------------------------------------------------------
-- 7. Append-only temporal semantics.
--
-- Revoking metric use stops future derivation/admission.  It does not claim to
-- rewrite the source audio, verbatim transcript or historical edit events.
------------------------------------------------------------------------

data RevocationRewritesVerbatimHistory : Set where
revocationDoesNotRewriteVerbatimHistory : RevocationRewritesVerbatimHistory → ⊥
revocationDoesNotRewriteVerbatimHistory ()

data DerivedMetricMayRewriteEditLedger : Set where
derivedMetricMayNotRewriteEditLedger : DerivedMetricMayRewriteEditLedger → ⊥
derivedMetricMayNotRewriteEditLedger ()

------------------------------------------------------------------------
-- 8. Existing-owner anchors.
------------------------------------------------------------------------

embodiedInteroceptionBoundaryAnchor : Embodied.EmbodiedOptionConeBoundary
embodiedInteroceptionBoundaryAnchor = Embodied.canonicalEmbodiedOptionConeBoundary

refreshCalibrationBoundaryAnchor : Refresh.InteroceptiveRefreshBoundary
refreshCalibrationBoundaryAnchor = Refresh.canonicalInteroceptiveRefreshBoundary

antiPanopticonBoundaryAnchor : Anti.AntiPanopticonBoundary
antiPanopticonBoundaryAnchor = Anti.canonicalAntiPanopticonBoundary

------------------------------------------------------------------------
-- 9. Canonical integration boundary.
------------------------------------------------------------------------

record TiRCorderVoiceEditInteroceptionBoundary : Set where
  constructor tiRCorderVoiceEditInteroceptionBoundary
  field
    verbatimAndRenderedAreDistinctCarriers : Bool
    editEventsRemainInspectablyProvenanced : Bool
    unresolvedIntentExecutesAutomatically : Bool
    correctionCountIsDiagnosis : Bool
    correctionCountIsCompetenceScore : Bool
    metricDerivationRequiresOptIn : Bool
    externalMetricExportRequiresSeparateOptIn : Bool
    observationCreatesInterventionAuthority : Bool
    metricMayRewriteHistoricalTranscript : Bool
    userMayUseMetricForPersonalReflection : Bool

canonicalTiRCorderVoiceEditInteroceptionBoundary :
  TiRCorderVoiceEditInteroceptionBoundary
canonicalTiRCorderVoiceEditInteroceptionBoundary =
  tiRCorderVoiceEditInteroceptionBoundary
    true
    true
    false
    false
    false
    true
    true
    false
    false
    true
