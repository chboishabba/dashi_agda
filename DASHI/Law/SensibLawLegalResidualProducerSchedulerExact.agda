module DASHI.Law.SensibLawLegalResidualProducerSchedulerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Law.SensibLawProductionLegalRuntimeABIExact as Runtime

------------------------------------------------------------------------
-- LEGAL RESIDUAL -> PRODUCER SCHEDULER
--
-- Formal counterpart of the bounded legal-adjunct/follow discipline.  A local
-- parser predicate never creates legal work by itself.  Legal acquisition or
-- review is activated only by an explicit legal residual and the coordinates
-- required by the selected producer.
------------------------------------------------------------------------

data LegalResidualKind : Set where
  legalRelevanceUnresolved : LegalResidualKind
  legalAuthorityAbsent : LegalResidualKind
  legalApplicabilityUnresolved : LegalResidualKind
  legalInterpretationUnresolved : LegalResidualKind
  legalElementPaymentMissing : LegalResidualKind


data LegalResidualDisposition : Set where
  residualOpen : LegalResidualDisposition
  residualBlocked : LegalResidualDisposition
  residualClosed : LegalResidualDisposition


producerForResidual : LegalResidualKind → Runtime.RuntimeLegalProducer
producerForResidual legalRelevanceUnresolved = Runtime.legalSourceFollowProducer
producerForResidual legalAuthorityAbsent = Runtime.legalSourceFollowProducer
producerForResidual legalApplicabilityUnresolved = Runtime.applicabilityReviewProducer
producerForResidual legalInterpretationUnresolved = Runtime.wrongTypeElementProducer
producerForResidual legalElementPaymentMissing = Runtime.evidencePaymentProducer

------------------------------------------------------------------------
-- Source-follow readiness is a product, not a guessed URL search.
------------------------------------------------------------------------

record LegalSourcePlanReadiness : Set₁ where
  constructor legalSourcePlanReadiness
  field
    structuralSignatureReference : String
    jurisdictionReference : String
    sourceRoleReference : String
    authorityLevelReference : String
    temporalEnvelopeReference : String

    structuralSignaturePresentReceipt : Set
    jurisdictionPresentReceipt : Set
    sourceRolePresentReceipt : Set
    authorityLevelPresentReceipt : Set

    planReference : String

open LegalSourcePlanReadiness public

record LegalResidualDemand : Set₁ where
  constructor legalResidualDemand
  field
    residual : LegalResidualKind
    disposition : LegalResidualDisposition
    producer : Runtime.RuntimeLegalProducer
    producerMatchesResidual : producer ≡ producerForResidual residual
    sourcePlan : LegalSourcePlanReadiness
    demandReference : String

open LegalResidualDemand public

------------------------------------------------------------------------
-- Blocked demand keeps the missing coordinate explicit.  It may not broaden
-- to a generic jurisdiction crawl.
------------------------------------------------------------------------

data MissingLegalPlanCoordinate : Set where
  missingStructuralSignature : MissingLegalPlanCoordinate
  missingJurisdiction : MissingLegalPlanCoordinate
  missingSourceRole : MissingLegalPlanCoordinate
  missingAuthorityLevel : MissingLegalPlanCoordinate


record BlockedLegalResidualDemand : Set where
  constructor blockedLegalResidualDemand
  field
    residual : LegalResidualKind
    missingCoordinate : MissingLegalPlanCoordinate
    blockedProducer : Runtime.RuntimeLegalProducer
    blockedProducerMatchesResidual :
      blockedProducer ≡ producerForResidual residual
    blockedReference : String

open BlockedLegalResidualDemand public

------------------------------------------------------------------------
-- Follow execution receipt remains acquisition-only.
------------------------------------------------------------------------

record BoundedLegalFollowReceipt (demand : LegalResidualDemand) : Set₁ where
  constructor boundedLegalFollowReceipt
  field
    selectedEndpointReference : String
    selectedEndpointMatchesJurisdictionReceipt : Set
    selectedEndpointMatchesSourceRoleReceipt : Set
    selectedEndpointMatchesAuthorityLevelReceipt : Set
    boundedAcquisitionReceipt : Set

    acquisitionAuthorizesTruth : Bool
    acquisitionAuthorizesTruthIsFalse : acquisitionAuthorizesTruth ≡ false

    acquisitionAuthorizesApplicability : Bool
    acquisitionAuthorizesApplicabilityIsFalse :
      acquisitionAuthorizesApplicability ≡ false

    acquisitionReference : String

open BoundedLegalFollowReceipt public

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data OrdinaryPredicateAutomaticallyLegalResidual : Set where
data BlockedDemandMayBroadenJurisdiction : Set where
data SourceFollowAutomaticallyApplicable : Set where
data SourceFollowAutomaticallyTruth : Set where
data EndpointAuthorityLevelAutomaticallyLegalHolding : Set where

ordinaryPredicateDoesNotCreateLegalResidual :
  OrdinaryPredicateAutomaticallyLegalResidual → ⊥
ordinaryPredicateDoesNotCreateLegalResidual ()

blockedDemandDoesNotPermitBroadening :
  BlockedDemandMayBroadenJurisdiction → ⊥
blockedDemandDoesNotPermitBroadening ()

sourceFollowDoesNotCreateApplicability :
  SourceFollowAutomaticallyApplicable → ⊥
sourceFollowDoesNotCreateApplicability ()

sourceFollowDoesNotCreateTruth :
  SourceFollowAutomaticallyTruth → ⊥
sourceFollowDoesNotCreateTruth ()

endpointAuthorityLevelDoesNotCreateHolding :
  EndpointAuthorityLevelAutomaticallyLegalHolding → ⊥
endpointAuthorityLevelDoesNotCreateHolding ()

record LegalResidualSchedulerBoundary : Set where
  constructor legalResidualSchedulerBoundary
  field
    legalWorkRequiresExplicitLegalResidual : Bool
    legalWorkRequiresExplicitLegalResidualIsTrue :
      legalWorkRequiresExplicitLegalResidual ≡ true

    sourceFollowRequiresTypedPlan : Bool
    sourceFollowRequiresTypedPlanIsTrue : sourceFollowRequiresTypedPlan ≡ true

    blockedPlanBroadensSearch : Bool
    blockedPlanBroadensSearchIsFalse : blockedPlanBroadensSearch ≡ false

    acquisitionEqualsLegalConclusion : Bool
    acquisitionEqualsLegalConclusionIsFalse :
      acquisitionEqualsLegalConclusion ≡ false

canonicalLegalResidualSchedulerBoundary : LegalResidualSchedulerBoundary
canonicalLegalResidualSchedulerBoundary =
  legalResidualSchedulerBoundary true refl true refl false refl false refl
