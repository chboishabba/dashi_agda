module DASHI.Interop.SensibLawNatSourceSupportAcquisitionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Interop.SensibLawWikidataReferenceRoleAuthorityExact as ReferenceRole
import DASHI.Interop.SensibLawWikidataBalancedTernaryAdmissibilityHyperfabricExact as Ternary

------------------------------------------------------------------------
-- NAT SOURCE SUPPORT: REFERENCE != CONTENT != SUPPORT != AUTHORITY
--
-- Runtime counterpart:
--   exact row/statement
--     -> P854 source candidate
--     -> deduplicated physical fetch
--     -> content/integrity observation
--     -> proposition-support evaluation (still downstream)
--     -> authority evaluation (still downstream)
--
-- Physical sharing never merges consumer-relative residual identity.
------------------------------------------------------------------------

record NatSourceSupportResidual : Set where
  constructor natSourceSupportResidual
  field
    sourceRowReference : String
    subjectQidReference : String
    statementReference : String
    consumerReference : String
    residualReference : String
open NatSourceSupportResidual public

record SourceFetchDemand (residual : NatSourceSupportResidual) : Set where
  constructor sourceFetchDemand
  field
    referenceURL : String
    selectedReferenceRole : ReferenceRole.ReferenceRole
    selectedReferenceIsSourceCandidate :
      selectedReferenceRole ≡ ReferenceRole.sourceCandidate
    boundResidualReference : String
    boundResidualIsExact :
      boundResidualReference ≡ residualReference residual
    contentAcquisitionOnly : Bool
    contentAcquisitionOnlyIsTrue : contentAcquisitionOnly ≡ true
open SourceFetchDemand public

record SourceFetchReceipt
    {residual : NatSourceSupportResidual}
    (demand : SourceFetchDemand residual) : Set where
  constructor sourceFetchReceipt
  field
    observedReferenceURL : String
    observedReferenceIsExact : observedReferenceURL ≡ referenceURL demand
    contentAcquired : Bool
    contentIntegrityObserved : Bool
    bytesObserved : Bool
    sourceSupportPaid : Bool
    sourceSupportPaidIsFalse : sourceSupportPaid ≡ false
    semanticPromotionPerformed : Bool
    semanticPromotionPerformedIsFalse : semanticPromotionPerformed ≡ false
open SourceFetchReceipt public

record SourceSupportObservation
    (residual : NatSourceSupportResidual) : Set where
  constructor sourceSupportObservation
  field
    referencePresent : Ternary.AdmissibilityState
    contentAcquisition : Ternary.AdmissibilityState
    propositionSupport : Ternary.AdmissibilityState
    authority : Ternary.AdmissibilityState
    propositionSupportStillOpen : propositionSupport ≡ Ternary.open
    authorityStillOpen : authority ≡ Ternary.open
    sourceSupportPaid : Bool
    sourceSupportPaidIsFalse : sourceSupportPaid ≡ false
open SourceSupportObservation public

-- A fetched, integrity-observed source may advance the transport/content fibres
-- without changing the proposition-support or authority fibres.
canonicalFetchedSourceObservation :
  (residual : NatSourceSupportResidual) → SourceSupportObservation residual
canonicalFetchedSourceObservation residual =
  sourceSupportObservation
    Ternary.admitted
    Ternary.admitted
    Ternary.open
    Ternary.open
    refl
    refl
    false
    refl

------------------------------------------------------------------------
-- FIREWALLS
------------------------------------------------------------------------

data ReferencePresencePaysSourceSupport : Set where
data ContentAcquisitionPaysSourceSupport : Set where
data ContentDigestPaysSourceSupport : Set where
data SharedFetchMergesResidualIdentity : Set where
data SourceSupportCreatesAuthority : Set where

aReferencePresenceDoesNotPaySourceSupport :
  ReferencePresencePaysSourceSupport → ⊥
aReferencePresenceDoesNotPaySourceSupport ()

contentAcquisitionDoesNotPaySourceSupport :
  ContentAcquisitionPaysSourceSupport → ⊥
contentAcquisitionDoesNotPaySourceSupport ()

contentDigestDoesNotPaySourceSupport :
  ContentDigestPaysSourceSupport → ⊥
contentDigestDoesNotPaySourceSupport ()

sharedFetchDoesNotMergeResidualIdentity :
  SharedFetchMergesResidualIdentity → ⊥
sharedFetchDoesNotMergeResidualIdentity ()

sourceSupportDoesNotCreateAuthority : SourceSupportCreatesAuthority → ⊥
sourceSupportDoesNotCreateAuthority ()

record NatSourceSupportAcquisitionBoundary : Set where
  constructor nat-source-support-acquisition-boundary
  field
    p854IsOnlySourceCandidate : Bool
    exactRowStatementBindingRequired : Bool
    duplicateUrlsMaySharePhysicalFetch : Bool
    sharedFetchMergesResiduals : Bool
    fetchedContentPaysSourceSupport : Bool
    contentDigestPaysSourceSupport : Bool
    propositionSupportNeedsSeparateEvaluation : Bool
    authorityNeedsSeparateEvaluation : Bool
    networkTelemetryIsFirstClass : Bool
    semanticPromotionCreatedByFetch : Bool

canonicalNatSourceSupportAcquisitionBoundary : NatSourceSupportAcquisitionBoundary
canonicalNatSourceSupportAcquisitionBoundary =
  nat-source-support-acquisition-boundary
    true true true false false false true true true false
