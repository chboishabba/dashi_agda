module DASHI.Core.SourceConditionedObservationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- GENERIC SOURCE-CONDITIONED OBSERVATION CORE
--
-- This is deliberately domain-neutral.  A statute, judgment, recording,
-- health record, wearable sample, environmental measurement, email, or
-- housing document may all instantiate the same carrier.
--
--   artifact existence
--     != proposition support
--     != canonical identity
--     != promotion / downstream payment.
------------------------------------------------------------------------

data SourceArtifactKind : Set where
  documentaryArtifact : SourceArtifactKind
  recordingArtifact : SourceArtifactKind
  measurementArtifact : SourceArtifactKind
  derivedArtifact : SourceArtifactKind
  externalSystemArtifact : SourceArtifactKind

record SourceArtifact : Set where
  constructor sourceArtifact
  field
    artifactId : String
    artifactKind : SourceArtifactKind
    carrierReference : String
    sourceSystemReference : String

open SourceArtifact public

record ProvenanceAnchor (artifact : SourceArtifact) : Set where
  constructor provenanceAnchor
  field
    provenanceReference : String
    timestampReference : String
    identityReference : String
    provenanceReceipt : Set

open ProvenanceAnchor public

record SourceConditionedObservation
    (Observation : Set)
    (o : Observation) : Set₁ where
  constructor sourceConditionedObservation
  field
    source : SourceArtifact
    provenance : ProvenanceAnchor source
    sourceSupportsObservation : Set
    supportReference : String

open SourceConditionedObservation public

record CanonicalObservationIdentity
    {Observation : Set}
    (left right : Observation) : Set₁ where
  constructor canonicalObservationIdentity
  field
    sameObjectReceipt : Set
    identityReference : String

open CanonicalObservationIdentity public

record TimeSeriesObservation : Set₁ where
  constructor timeSeriesObservation
  field
    subjectReference : String
    metricReference : String
    timestampReference : String
    valueReference : String
    unitReference : String
    source : SourceArtifact
    provenance : ProvenanceAnchor source
    observationReceipt : Set

open TimeSeriesObservation public

------------------------------------------------------------------------
-- Core firewalls.
------------------------------------------------------------------------

data ArtifactExistenceAutomaticallySupportsObservation : Set where
data SourceSupportAutomaticallyCanonicalIdentity : Set where
data CanonicalIdentityAutomaticallyPromoted : Set where

data TimeSeriesObservationAutomaticallyDiagnosis : Set where

artifactExistenceDoesNotAutoSupportObservation :
  ArtifactExistenceAutomaticallySupportsObservation → ⊥
artifactExistenceDoesNotAutoSupportObservation ()

sourceSupportDoesNotAutoResolveCanonicalIdentity :
  SourceSupportAutomaticallyCanonicalIdentity → ⊥
sourceSupportDoesNotAutoResolveCanonicalIdentity ()

canonicalIdentityDoesNotAutoPromote :
  CanonicalIdentityAutomaticallyPromoted → ⊥
canonicalIdentityDoesNotAutoPromote ()

timeSeriesObservationDoesNotAutoDiagnose :
  TimeSeriesObservationAutomaticallyDiagnosis → ⊥
timeSeriesObservationDoesNotAutoDiagnose ()

record SourceConditionedObservationBoundary : Set where
  constructor sourceConditionedObservationBoundary
  field
    artifactAndSupportAreSeparated : Bool
    artifactAndSupportAreSeparatedIsTrue :
      artifactAndSupportAreSeparated ≡ true
    supportAndIdentityAreSeparated : Bool
    supportAndIdentityAreSeparatedIsTrue :
      supportAndIdentityAreSeparated ≡ true
    identityAndPromotionAreSeparated : Bool
    identityAndPromotionAreSeparatedIsTrue :
      identityAndPromotionAreSeparated ≡ true
    timeSeriesDoesNotEncodeDiagnosis : Bool
    timeSeriesDoesNotEncodeDiagnosisIsTrue :
      timeSeriesDoesNotEncodeDiagnosis ≡ true

canonicalSourceConditionedObservationBoundary :
  SourceConditionedObservationBoundary
canonicalSourceConditionedObservationBoundary =
  sourceConditionedObservationBoundary
    true refl
    true refl
    true refl
    true refl
