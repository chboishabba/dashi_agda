module DASHI.Law.SensibLawHealthRecordEvidenceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.SourceConditionedObservationExact as Observation

------------------------------------------------------------------------
-- GENERIC HEALTH-RECORD EVIDENCE ALGEBRA
--
-- A medical/health artifact is not a proposition, and a proposition supported
-- by that artifact is not automatically the same pleaded harm or a causal
-- conclusion.  This owner is generic; Herries/Brighton/Chapel Hill remain
-- downstream fixtures.
------------------------------------------------------------------------

data HealthArtifactKind : Set where
  clinicalReport : HealthArtifactKind
  consultationNote : HealthArtifactKind
  pathologyResult : HealthArtifactKind
  medicationRecord : HealthArtifactKind
  physiologicalTable : HealthArtifactKind
  wearableSeries : HealthArtifactKind
  selfReport : HealthArtifactKind
  carerAssessment : HealthArtifactKind
  costRecord : HealthArtifactKind

record HealthRecordArtifact : Set₁ where
  constructor healthRecordArtifact
  field
    sourceArtifact : Observation.SourceArtifact
    artifactKind : HealthArtifactKind
    subjectReference : String
    providerOrAuthorReference : String
    recordedAtReference : String
    effectivePeriodReference : String
    provenance : Observation.ProvenanceAnchor sourceArtifact

open HealthRecordArtifact public

data HealthAtomKind : Set where
  conditionPresent : HealthAtomKind
  symptomObserved : HealthAtomKind
  measurementObserved : HealthAtomKind
  functionalLimitation : HealthAtomKind
  treatmentReceived : HealthAtomKind
  careRequired : HealthAtomKind
  aggravationOccurred : HealthAtomKind
  causedByEvent : HealthAtomKind

record HealthAtom : Set where
  constructor healthAtom
  field
    atomKind : HealthAtomKind
    subjectReference : String
    predicateReference : String
    objectReference : String
    temporalReference : String

open HealthAtom public

record SourceConditionedHealthAtom (atom : HealthAtom) : Set₁ where
  constructor sourceConditionedHealthAtom
  field
    recordArtifact : HealthRecordArtifact
    observation : Observation.SourceConditionedObservation HealthAtom atom
    authorityReference : String

open SourceConditionedHealthAtom public

------------------------------------------------------------------------
-- Particular-harm identity comes before legal causation.
------------------------------------------------------------------------

record ParticularHarmIdentityWeld : Set₁ where
  constructor particularHarmIdentityWeld
  field
    pleadedHarmReference : String
    clinicalHarmAtom : HealthAtom
    sameSubjectReceipt : Set
    sameHarmTypeReceipt : Set
    temporalFitReceipt : Set
    identityEvidenceReceipt : Set
    weldReference : String

open ParticularHarmIdentityWeld public

record FactualCausationEvidence
    (weld : ParticularHarmIdentityWeld) : Set₁ where
  constructor factualCausationEvidence
  field
    eventReference : String
    causalSourceArtifact : Observation.SourceArtifact
    causalLinkReceipt : Set
    authorityReference : String
    evidenceReference : String

open FactualCausationEvidence public

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data HealthArtifactAutomaticallyHealthAtom : Set where
data HealthAtomAutomaticallyParticularHarm : Set where
data ParticularHarmAutomaticallyCausation : Set where
data CausationAutomaticallyScope : Set where
data ScopeAutomaticallyProvesDamagesAmount : Set where

ahealthArtifactDoesNotAutoBecomeAtom :
  HealthArtifactAutomaticallyHealthAtom → ⊥
ahealthArtifactDoesNotAutoBecomeAtom ()

healthAtomDoesNotAutoIdentifyParticularHarm :
  HealthAtomAutomaticallyParticularHarm → ⊥
healthAtomDoesNotAutoIdentifyParticularHarm ()

particularHarmDoesNotAutoPayCausation :
  ParticularHarmAutomaticallyCausation → ⊥
particularHarmDoesNotAutoPayCausation ()

causationDoesNotAutoPayScope : CausationAutomaticallyScope → ⊥
causationDoesNotAutoPayScope ()

scopeDoesNotAutoProveDamagesAmount :
  ScopeAutomaticallyProvesDamagesAmount → ⊥
scopeDoesNotAutoProveDamagesAmount ()

record HealthRecordEvidenceBoundary : Set where
  constructor healthRecordEvidenceBoundary
  field
    artifactKindAndPropositionKindSeparated : Bool
    artifactKindAndPropositionKindSeparatedIsTrue :
      artifactKindAndPropositionKindSeparated ≡ true
    particularHarmRequiresIdentityWeld : Bool
    particularHarmRequiresIdentityWeldIsTrue :
      particularHarmRequiresIdentityWeld ≡ true
    factualCausationRequiresIndependentEvidence : Bool
    factualCausationRequiresIndependentEvidenceIsTrue :
      factualCausationRequiresIndependentEvidence ≡ true
    scopeRequiresIndependentPayment : Bool
    scopeRequiresIndependentPaymentIsTrue :
      scopeRequiresIndependentPayment ≡ true
    damagesAmountRequiresIndependentProof : Bool
    damagesAmountRequiresIndependentProofIsTrue :
      damagesAmountRequiresIndependentProof ≡ true

canonicalHealthRecordEvidenceBoundary : HealthRecordEvidenceBoundary
canonicalHealthRecordEvidenceBoundary =
  healthRecordEvidenceBoundary
    true refl
    true refl
    true refl
    true refl
    true refl
