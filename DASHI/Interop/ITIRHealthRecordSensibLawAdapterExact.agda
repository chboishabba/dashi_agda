module DASHI.Interop.ITIRHealthRecordSensibLawAdapterExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.SourceConditionedObservationExact as Observation
import DASHI.Interop.ITIRSuiteNormalizedCompilerParityExact as ITIR
import DASHI.Law.SensibLawHealthRecordEvidenceExact as Health
import DASHI.Law.SensibLawLongitudinalHousingHealthExact as Longitudinal

------------------------------------------------------------------------
-- GENERIC HEALTH RECORD -> ITIR -> SENSIBLAW
--
-- Provider-specific data normalize only after provenance is retained.  A
-- physiological observation is an observed signal; a same-harm relation is a
-- reviewable claim; promotion and legal causation remain separate receipts.
------------------------------------------------------------------------

record ITIRHealthRecordObservation : Set₁ where
  constructor itirHealthRecordObservation
  field
    healthArtifact : Health.HealthRecordArtifact
    healthAtom : Health.HealthAtom
    sourceArtifact : ITIR.NormalizedArtifact
    provenanceArtifact : ITIR.NormalizedArtifact
    observedArtifact : ITIR.NormalizedArtifact
    reviewableArtifact : ITIR.NormalizedArtifact
    sourceIsArtifact : ITIR.concept sourceArtifact ≡ ITIR.sourceArtifact
    provenanceIsAnchor :
      ITIR.concept provenanceArtifact ≡ ITIR.provenanceAnchor
    observationIsSignal : ITIR.concept observedArtifact ≡ ITIR.observedSignal
    healthClaimIsReviewable :
      ITIR.concept reviewableArtifact ≡ ITIR.reviewableClaim
    sourceConditioningReceipt : Set
    adapterReference : String

open ITIRHealthRecordObservation public

record ITIRParticularHarmIdentity
    (observation : ITIRHealthRecordObservation) : Set₁ where
  constructor itirParticularHarmIdentity
  field
    harmWeld : Health.ParticularHarmIdentityWeld
    canonicalIdentityArtifact : ITIR.NormalizedArtifact
    reviewableIdentityClaim : ITIR.NormalizedArtifact
    identityIsCanonical :
      ITIR.concept canonicalIdentityArtifact ≡ ITIR.canonicalIdentity
    identityClaimIsReviewable :
      ITIR.concept reviewableIdentityClaim ≡ ITIR.reviewableClaim
    identityCompilationReceipt : Set
    identityReference : String

open ITIRParticularHarmIdentity public

record PromotedITIRParticularHarm
    {observation : ITIRHealthRecordObservation}
    (identity : ITIRParticularHarmIdentity observation) : Set₁ where
  constructor promotedITIRParticularHarm
  field
    promotedArtifact : ITIR.NormalizedArtifact
    promotedIsRecord : ITIR.concept promotedArtifact ≡ ITIR.promotedRecord
    promotionReceipt :
      ITIR.PromotionReceipt
        (ITIRParticularHarmIdentity.reviewableIdentityClaim identity)
        promotedArtifact
    promotionReference : String

open PromotedITIRParticularHarm public

record ITIRLongitudinalHousingHealthClaim : Set₁ where
  constructor itirLongitudinalHousingHealthClaim
  field
    sequence : Longitudinal.LongitudinalHealthHousingSequence
    compiledStateArtifact : ITIR.NormalizedArtifact
    reviewableCrossEpisodeClaim : ITIR.NormalizedArtifact
    sequenceIsCompiledState :
      ITIR.concept compiledStateArtifact ≡ ITIR.compiledState
    crossEpisodeClaimIsReviewable :
      ITIR.concept reviewableCrossEpisodeClaim ≡ ITIR.reviewableClaim
    compilationReceipt : Set
    claimReference : String

open ITIRLongitudinalHousingHealthClaim public

------------------------------------------------------------------------
-- Parity boundary and firewalls.
------------------------------------------------------------------------

record ITIRHealthRecordParityBoundary : Set where
  constructor itirHealthRecordParityBoundary
  field
    providerDataRetainsProvenance : Bool
    providerDataRetainsProvenanceIsTrue :
      providerDataRetainsProvenance ≡ true
    physiologicalSampleStartsAsObservedSignal : Bool
    physiologicalSampleStartsAsObservedSignalIsTrue :
      physiologicalSampleStartsAsObservedSignal ≡ true
    sameHarmIdentityStartsReviewable : Bool
    sameHarmIdentityStartsReviewableIsTrue :
      sameHarmIdentityStartsReviewable ≡ true
    promotionRequiresReceipt : Bool
    promotionRequiresReceiptIsTrue : promotionRequiresReceipt ≡ true
    promotedHarmAutomaticallyPaysCausation : Bool
    promotedHarmAutomaticallyPaysCausationIsFalse :
      promotedHarmAutomaticallyPaysCausation ≡ false
    longitudinalPatternAutomaticallyCommonCause : Bool
    longitudinalPatternAutomaticallyCommonCauseIsFalse :
      longitudinalPatternAutomaticallyCommonCause ≡ false

canonicalITIRHealthRecordParityBoundary : ITIRHealthRecordParityBoundary
canonicalITIRHealthRecordParityBoundary =
  itirHealthRecordParityBoundary
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl

data ProviderNormalizationDropsProvenance : Set where
data ObservedSignalAutomaticallyDiagnosis : Set where
data SameHarmIdentityBypassesPromotion : Set where
data PromotedHarmAutomaticallyPaysCausation : Set where
data LongitudinalPatternAutomaticallyCommonCause : Set where

providerNormalizationDoesNotDropProvenance :
  ProviderNormalizationDropsProvenance → ⊥
providerNormalizationDoesNotDropProvenance ()

observedSignalDoesNotAutoDiagnose : ObservedSignalAutomaticallyDiagnosis → ⊥
observedSignalDoesNotAutoDiagnose ()

sameHarmIdentityDoesNotBypassPromotion : SameHarmIdentityBypassesPromotion → ⊥
sameHarmIdentityDoesNotBypassPromotion ()

promotedHarmDoesNotAutoPayCausation :
  PromotedHarmAutomaticallyPaysCausation → ⊥
promotedHarmDoesNotAutoPayCausation ()

longitudinalPatternDoesNotAutoBecomeCommonCause :
  LongitudinalPatternAutomaticallyCommonCause → ⊥
longitudinalPatternDoesNotAutoBecomeCommonCause ()

selectedGenericObservationBoundary :
  Observation.SourceConditionedObservationBoundary
selectedGenericObservationBoundary =
  Observation.canonicalSourceConditionedObservationBoundary
