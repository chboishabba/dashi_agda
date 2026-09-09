module DASHI.Interop.ITIRTemporalHealthSensibLawAdapterExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Interop.ITIRSuiteNormalizedCompilerParityExact as ITIR
import DASHI.Law.SensibLawTemporalHealthEvidenceWrongTypeExact as Health
import DASHI.Law.SensibLawWrongTypeCausationElementExact as Element

------------------------------------------------------------------------
-- ITIR NORMALIZED SPINE -> SENSIBLAW TEMPORAL-HEALTH ADAPTER
--
-- ITIR owns the normalized source/provenance/observation/review/promotion
-- distinction. SensibLaw owns the legal evidence and WrongType consumers.
-- This adapter prevents the Russell fixture from becoming a second source or
-- identity ontology inside the legal layer.
------------------------------------------------------------------------

record ITIRHealthObservation : Set₁ where
  constructor itirHealthObservation
  field
    healthObservation : Health.HealthObservation
    sourceArtifact : ITIR.NormalizedArtifact
    observationArtifact : ITIR.NormalizedArtifact
    sourceIsArtifact : ITIR.concept sourceArtifact ≡ ITIR.sourceArtifact
    observationIsSignal : ITIR.concept observationArtifact ≡ ITIR.observedSignal
    sourceToObservationReceipt : Set
    adapterReference : String

open ITIRHealthObservation public

record ITIRDisputeEvent : Set₁ where
  constructor itirDisputeEvent
  field
    disputeEvent : Health.DisputeEvent
    eventSourceArtifact : ITIR.NormalizedArtifact
    compiledEventState : ITIR.NormalizedArtifact
    sourceIsArtifact : ITIR.concept eventSourceArtifact ≡ ITIR.sourceArtifact
    stateIsCompiled : ITIR.concept compiledEventState ≡ ITIR.compiledState
    eventCompilationReceipt : Set
    adapterReference : String

open ITIRDisputeEvent public

record ITIRTemporalCorrelationClaim
    (observation : ITIRHealthObservation)
    (event : ITIRDisputeEvent) : Set₁ where
  constructor itirTemporalCorrelationClaim
  field
    correlation :
      Health.TemporalHealthCorrelation
        (ITIRHealthObservation.healthObservation observation)
        (ITIRDisputeEvent.disputeEvent event)
    claimArtifact : ITIR.NormalizedArtifact
    claimIsReviewable : ITIR.concept claimArtifact ≡ ITIR.reviewableClaim
    correlationToClaimReceipt : Set
    claimReference : String

open ITIRTemporalCorrelationClaim public

------------------------------------------------------------------------
-- Legal admission and factual-causation payment remain downstream.
------------------------------------------------------------------------

record ITIRWrongTypeHealthAdmission
    {declaration : Element.WrongTypeCausationElementDeclaration}
    (weld : Element.ViolationWrongTypeCausationElementWeld declaration) : Set₁ where
  constructor itirWrongTypeHealthAdmission
  field
    legalEvidence : Health.WrongTypeTemporalHealthEvidence weld
    reviewableClaim : ITIR.NormalizedArtifact
    reviewableClaimIsReviewable :
      ITIR.concept reviewableClaim ≡ ITIR.reviewableClaim
    admissionReceipt : Set
    admissionReference : String

open ITIRWrongTypeHealthAdmission public

record ITIRWrongTypeHealthPayment
    {declaration : Element.WrongTypeCausationElementDeclaration}
    {weld : Element.ViolationWrongTypeCausationElementWeld declaration}
    (admission : ITIRWrongTypeHealthAdmission weld) : Set₁ where
  constructor itirWrongTypeHealthPayment
  field
    legalPayment :
      Health.TemporalHealthEvidencePayment
        (ITIRWrongTypeHealthAdmission.legalEvidence admission)
    promotedArtifact : ITIR.NormalizedArtifact
    promotedIsRecord : ITIR.concept promotedArtifact ≡ ITIR.promotedRecord
    promotionReceipt :
      ITIR.PromotionReceipt
        (ITIRWrongTypeHealthAdmission.reviewableClaim admission)
        promotedArtifact
    paymentReference : String

open ITIRWrongTypeHealthPayment public

------------------------------------------------------------------------
-- Parity boundary.
------------------------------------------------------------------------

record ITIRTemporalHealthSensibLawParityBoundary : Set where
  constructor itirTemporalHealthSensibLawParityBoundary
  field
    measurementStartsAsObservedSignal : Bool
    measurementStartsAsObservedSignalIsTrue :
      measurementStartsAsObservedSignal ≡ true

    temporalCorrelationStartsAsReviewableClaim : Bool
    temporalCorrelationStartsAsReviewableClaimIsTrue :
      temporalCorrelationStartsAsReviewableClaim ≡ true

    correlationMayBypassPromotion : Bool
    correlationMayBypassPromotionIsFalse : correlationMayBypassPromotion ≡ false

    legalAdmissionAutomaticallyPaysCausation : Bool
    legalAdmissionAutomaticallyPaysCausationIsFalse :
      legalAdmissionAutomaticallyPaysCausation ≡ false

    sensibLawMayInventUpstreamSourceIdentity : Bool
    sensibLawMayInventUpstreamSourceIdentityIsFalse :
      sensibLawMayInventUpstreamSourceIdentity ≡ false

canonicalITIRTemporalHealthSensibLawParityBoundary :
  ITIRTemporalHealthSensibLawParityBoundary
canonicalITIRTemporalHealthSensibLawParityBoundary =
  itirTemporalHealthSensibLawParityBoundary
    true refl
    true refl
    false refl
    false refl
    false refl

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data CorrelationBypassesPromotion : Set where
data AdmissionAutomaticallyPaysCausation : Set where
data SensibLawInventsUpstreamSourceIdentity : Set where

correlationDoesNotBypassPromotion : CorrelationBypassesPromotion → ⊥
correlationDoesNotBypassPromotion ()

admissionDoesNotAutoPayCausation : AdmissionAutomaticallyPaysCausation → ⊥
admissionDoesNotAutoPayCausation ()

sensibLawDoesNotInventUpstreamSourceIdentity :
  SensibLawInventsUpstreamSourceIdentity → ⊥
sensibLawDoesNotInventUpstreamSourceIdentity ()
