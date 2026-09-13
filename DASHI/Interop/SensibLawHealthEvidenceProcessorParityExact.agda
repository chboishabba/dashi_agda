module DASHI.Interop.SensibLawHealthEvidenceProcessorParityExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.SourceConditionedObservationExact as Observation
import DASHI.Law.SensibLawHealthRecordEvidenceExact as Health

------------------------------------------------------------------------
-- SCRIPT <-> AGDA PARITY FOR HEALTH-EVIDENCE INGESTION
--
-- Operational owner:
--   scripts/process_sensiblaw_health_evidence.py
--
-- The script normalizes provider-specific health carriers and performs
-- temporal joins. It is a witness producer only. Agda owns the semantic
-- admission boundary: normalization and temporal proximity do not manufacture
-- diagnosis, particular-harm identity, factual causation, scope, or damages.
------------------------------------------------------------------------

processorPath : String
processorPath = "scripts/process_sensiblaw_health_evidence.py"

processorContractVersion : String
processorContractVersion = "sensiblaw-health-evidence-v2"


data ProcessorCommand : Set where
  googleHealthPoints : ProcessorCommand
  qcatTranscription : ProcessorCommand
  eventJoin : ProcessorCommand


data ProcessorArtifactKind : Set where
  normalizedObservationTSV : ProcessorArtifactKind
  sourceReceiptJSON : ProcessorArtifactKind
  temporalJoinTSV : ProcessorArtifactKind
  temporalJoinReceiptJSON : ProcessorArtifactKind

record ProcessorReceipt : Set₁ where
  constructor processorReceipt
  field
    command : ProcessorCommand
    sourceReference : String
    sourceDigestReference : String
    outputReference : String
    outputKind : ProcessorArtifactKind
    rowCountReference : String
    schemaReference : String
    executionReceipt : Set

open ProcessorReceipt public

------------------------------------------------------------------------
-- Normalized observation parity.
------------------------------------------------------------------------

record NormalizedObservationProjection : Set₁ where
  constructor normalizedObservationProjection
  field
    processorReceipt : ProcessorReceipt
    sourceArtifact : Observation.SourceArtifact
    subjectReference : String
    metricReference : String
    rawTimestampReference : String
    canonicalTimestampReference : String
    timestampStatusReference : String
    valueReference : String
    unitReference : String
    provenance : Observation.ProvenanceAnchor sourceArtifact
    sourceRowReference : String
    sourceColumnReference : String
    projectionReceipt : Set

open NormalizedObservationProjection public

asTimeSeriesObservation :
  NormalizedObservationProjection → Observation.TimeSeriesObservation
asTimeSeriesObservation projection =
  Observation.timeSeriesObservation
    (subjectReference projection)
    (metricReference projection)
    (canonicalTimestampReference projection)
    (valueReference projection)
    (unitReference projection)
    (sourceArtifact projection)
    (provenance projection)
    (projectionReceipt projection)

------------------------------------------------------------------------
-- Temporal join parity.
------------------------------------------------------------------------


data ProcessorTemporalRelation : Set where
  before : ProcessorTemporalRelation
  sameTimestamp : ProcessorTemporalRelation
  sameDay : ProcessorTemporalRelation
  nearAfter : ProcessorTemporalRelation
  after : ProcessorTemporalRelation
  unresolved : ProcessorTemporalRelation


data EventPrecision : Set where
  timestampPrecision : EventPrecision
  dayPrecision : EventPrecision


data JoinGranularity : Set where
  sourceRowGranularity : JoinGranularity
  metricGranularity : JoinGranularity

record ProcessorTemporalJoin : Set₁ where
  constructor processorTemporalJoin
  field
    observationReference : String
    eventReference : String
    relation : ProcessorTemporalRelation
    eventPrecision : EventPrecision
    joinGranularity : JoinGranularity
    deltaSecondsReference : String
    deltaDaysReference : String
    observationSourceDigestReference : String
    eventSourceDigestReference : String
    joinReceipt : Set

open ProcessorTemporalJoin public

------------------------------------------------------------------------
-- Fail-closed semantic parity.
------------------------------------------------------------------------

record HealthEvidenceProcessorParityBoundary : Set where
  constructor healthEvidenceProcessorParityBoundary
  field
    normalizationMayInferDiagnosis : Bool
    normalizationMayInferDiagnosisIsFalse :
      normalizationMayInferDiagnosis ≡ false

    normalizationMayInferCausation : Bool
    normalizationMayInferCausationIsFalse :
      normalizationMayInferCausation ≡ false

    missingValuesMayBeImputedSilently : Bool
    missingValuesMayBeImputedSilentlyIsFalse :
      missingValuesMayBeImputedSilently ≡ false

    rawSourceTimestampsMayBeMutated : Bool
    rawSourceTimestampsMayBeMutatedIsFalse :
      rawSourceTimestampsMayBeMutated ≡ false

    unsupportedProviderFieldsMayBePromoted : Bool
    unsupportedProviderFieldsMayBePromotedIsFalse :
      unsupportedProviderFieldsMayBePromoted ≡ false

    dayPrecisionMayInventClockTime : Bool
    dayPrecisionMayInventClockTimeIsFalse :
      dayPrecisionMayInventClockTime ≡ false

    temporalJoinMayPayParticularHarmIdentity : Bool
    temporalJoinMayPayParticularHarmIdentityIsFalse :
      temporalJoinMayPayParticularHarmIdentity ≡ false

    temporalJoinMayPayFactualCausation : Bool
    temporalJoinMayPayFactualCausationIsFalse :
      temporalJoinMayPayFactualCausation ≡ false

    rawPrivateNotesMayBeRepublishedByNormalization : Bool
    rawPrivateNotesMayBeRepublishedByNormalizationIsFalse :
      rawPrivateNotesMayBeRepublishedByNormalization ≡ false

canonicalHealthEvidenceProcessorParityBoundary :
  HealthEvidenceProcessorParityBoundary
canonicalHealthEvidenceProcessorParityBoundary =
  healthEvidenceProcessorParityBoundary
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data NormalizationAutomaticallyDiagnosis : Set where
data NormalizationAutomaticallyCausation : Set where
data TemporalJoinAutomaticallyParticularHarm : Set where
data TemporalJoinAutomaticallyCausation : Set where
data UnsupportedFieldAutomaticallyPromoted : Set where

data DayPrecisionAutomaticallyExactTime : Set where

normalizationDoesNotAutoDiagnose : NormalizationAutomaticallyDiagnosis → ⊥
normalizationDoesNotAutoDiagnose ()

normalizationDoesNotAutoCause : NormalizationAutomaticallyCausation → ⊥
normalizationDoesNotAutoCause ()

temporalJoinDoesNotAutoIdentifyParticularHarm :
  TemporalJoinAutomaticallyParticularHarm → ⊥
temporalJoinDoesNotAutoIdentifyParticularHarm ()

temporalJoinDoesNotAutoPayCausation :
  TemporalJoinAutomaticallyCausation → ⊥
temporalJoinDoesNotAutoPayCausation ()

unsupportedFieldDoesNotAutoPromote : UnsupportedFieldAutomaticallyPromoted → ⊥
unsupportedFieldDoesNotAutoPromote ()

dayPrecisionDoesNotInventExactTime : DayPrecisionAutomaticallyExactTime → ⊥
dayPrecisionDoesNotInventExactTime ()

------------------------------------------------------------------------
-- Consumer contract.
------------------------------------------------------------------------

record HealthEvidenceProcessorAdmission : Set₁ where
  constructor healthEvidenceProcessorAdmission
  field
    projection : NormalizedObservationProjection
    healthArtifact : Health.HealthRecordArtifact
    sameSourceCarrierReceipt : Set
    sameSubjectReceipt : Set
    admissionReference : String

open HealthEvidenceProcessorAdmission public

-- Admission to the generic health carrier is still not a health proposition.
data ProcessorAdmissionAutomaticallyHealthAtom : Set where

processorAdmissionDoesNotAutoBecomeHealthAtom :
  ProcessorAdmissionAutomaticallyHealthAtom → ⊥
processorAdmissionDoesNotAutoBecomeHealthAtom ()
