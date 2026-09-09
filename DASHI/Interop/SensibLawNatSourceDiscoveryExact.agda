module DASHI.Interop.SensibLawNatSourceDiscoveryExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Algebra.Trit as Trit
import DASHI.Interop.SensibLawWikidataBalancedTernaryAdmissibilityHyperfabricExact as Ternary
import DASHI.Interop.SensibLawNatSourceSupportAcquisitionExact as Source

------------------------------------------------------------------------
-- PROVIDER-NEUTRAL SOURCE DISCOVERY
--
-- Runtime counterpart:
--   failed/stale locator
--     -> exact source-discovery demand
--     -> Tavily / Google / Exa / MCP / human producer
--     -> locator candidates
--     -> separate same-source identity admission
--     -> existing source fetch transport
--
-- Search rank/snippet/title are discovery metadata only.  Discovery does not
-- pay same-source identity, proposition support, authority, or promotion.
------------------------------------------------------------------------

record SourceDiscoveryDemand
    (residual : Source.NatSourceSupportResidual) : Set where
  constructor sourceDiscoveryDemand
  field
    exactResidualReference : String
    exactResidualReferenceIsExact :
      exactResidualReference ≡ Source.residualReference residual
    failedFetchReference : String
    failedFetchReceiptReference : String
    originalLocator : String
    sourceIdentityReference : String
    querySeedReference : String
    demandReference : String
    providerNeutral : Bool
    providerNeutralIsTrue : providerNeutral ≡ true
    sameSourceIdentityRequired : Bool
    sameSourceIdentityRequiredIsTrue : sameSourceIdentityRequired ≡ true
open SourceDiscoveryDemand public

record LocatorCandidate
    {residual : Source.NatSourceSupportResidual}
    (demand : SourceDiscoveryDemand residual) : Set where
  constructor locatorCandidate
  field
    observedDemandReference : String
    observedDemandIsExact : observedDemandReference ≡ demandReference demand
    providerReference : String
    providerCallReference : String
    providerResultReference : String
    candidateLocator : String
    candidateTitle : String
    candidateSnippet : String
    candidateRankReference : String
    candidateReference : String
    sameSourceIdentityState : Ternary.AdmissibilityState
    sameSourceIdentityStillOpen : sameSourceIdentityState ≡ Ternary.open
    sourceSupportPaid : Bool
    sourceSupportPaidIsFalse : sourceSupportPaid ≡ false
open LocatorCandidate public

data SourceIdentityDisposition : Set where
  differentSource : SourceIdentityDisposition
  identityUnresolved : SourceIdentityDisposition
  sameSource : SourceIdentityDisposition

sourceIdentityTrit : SourceIdentityDisposition → Trit.Trit
sourceIdentityTrit differentSource = Trit.neg
sourceIdentityTrit identityUnresolved = Trit.zer
sourceIdentityTrit sameSource = Trit.pos

sourceIdentityAdmissibility : SourceIdentityDisposition → Ternary.AdmissibilityState
sourceIdentityAdmissibility differentSource = Ternary.rejected
sourceIdentityAdmissibility identityUnresolved = Ternary.open
sourceIdentityAdmissibility sameSource = Ternary.admitted

sameSourcePaid : SourceIdentityDisposition → Bool
sameSourcePaid differentSource = false
sameSourcePaid identityUnresolved = false
sameSourcePaid sameSource = true

record SameSourceIdentityReceipt
    {residual : Source.NatSourceSupportResidual}
    {demand : SourceDiscoveryDemand residual}
    (candidate : LocatorCandidate demand) : Set where
  constructor sameSourceIdentityReceipt
  field
    observedCandidateReference : String
    observedCandidateIsExact :
      observedCandidateReference ≡ candidateReference candidate
    disposition : SourceIdentityDisposition
    identityEvidenceLocator : String
    verifierReference : String
    identityState : Ternary.AdmissibilityState
    identityStateIsDisposition :
      identityState ≡ sourceIdentityAdmissibility disposition
    identityTrit : Trit.Trit
    identityTritIsDisposition : identityTrit ≡ sourceIdentityTrit disposition
    identityPaid : Bool
    identityPaidIsDisposition : identityPaid ≡ sameSourcePaid disposition
    sourceSupportPaid : Bool
    sourceSupportPaidIsFalse : sourceSupportPaid ≡ false
    authorityEvaluated : Bool
    authorityEvaluatedIsFalse : authorityEvaluated ≡ false
    semanticPromotionPerformed : Bool
    semanticPromotionPerformedIsFalse : semanticPromotionPerformed ≡ false
open SameSourceIdentityReceipt public

record AlternateLocatorFetchAdmission
    {residual : Source.NatSourceSupportResidual}
    {demand : SourceDiscoveryDemand residual}
    {candidate : LocatorCandidate demand}
    (identity : SameSourceIdentityReceipt candidate) : Set where
  constructor alternateLocatorFetchAdmission
  field
    selectedLocator : String
    selectedLocatorIsCandidate : selectedLocator ≡ candidateLocator candidate
    sameSourceIdentityPaid : Bool
    sameSourceIdentityPaidIsTrue : sameSourceIdentityPaid ≡ true
    contentAcquisitionOnly : Bool
    contentAcquisitionOnlyIsTrue : contentAcquisitionOnly ≡ true
    sourceSupportPaid : Bool
    sourceSupportPaidIsFalse : sourceSupportPaid ≡ false
open AlternateLocatorFetchAdmission public

admitAlternateLocator :
  {residual : Source.NatSourceSupportResidual} →
  {demand : SourceDiscoveryDemand residual} →
  {candidate : LocatorCandidate demand} →
  (identity : SameSourceIdentityReceipt candidate) →
  disposition identity ≡ sameSource →
  AlternateLocatorFetchAdmission identity
admitAlternateLocator {candidate = candidate} identity refl =
  alternateLocatorFetchAdmission
    (candidateLocator candidate)
    refl
    true
    refl
    true
    refl
    false
    refl

sameSourceMapsPositive : sourceIdentityTrit sameSource ≡ Trit.pos
sameSourceMapsPositive = refl

differentSourceMapsNegative : sourceIdentityTrit differentSource ≡ Trit.neg
differentSourceMapsNegative = refl

identityUnresolvedMapsZero : sourceIdentityTrit identityUnresolved ≡ Trit.zer
identityUnresolvedMapsZero = refl

data DiscoveryCandidatePaysSameSourceIdentity : Set where
data SearchRankPaysSourceSupport : Set where
data SearchSnippetPaysSourceSupport : Set where
data AlternateLocatorPaysSameSourceWithoutReceipt : Set where
data DifferentCandidateMeansHistoricalSourceAbsent : Set where
data DiscoveryFailureMeansHistoricalSourceAbsent : Set where
data SameSourceIdentityPaysPropositionSupport : Set where
data SameSourceIdentityCreatesAuthority : Set where

discoveryCandidateDoesNotPaySameSourceIdentity :
  DiscoveryCandidatePaysSameSourceIdentity → ⊥
discoveryCandidateDoesNotPaySameSourceIdentity ()

searchRankDoesNotPaySourceSupport : SearchRankPaysSourceSupport → ⊥
searchRankDoesNotPaySourceSupport ()

searchSnippetDoesNotPaySourceSupport : SearchSnippetPaysSourceSupport → ⊥
searchSnippetDoesNotPaySourceSupport ()

alternateLocatorNeedsIdentityReceipt :
  AlternateLocatorPaysSameSourceWithoutReceipt → ⊥
alternateLocatorNeedsIdentityReceipt ()

differentCandidateDoesNotEraseHistoricalSource :
  DifferentCandidateMeansHistoricalSourceAbsent → ⊥
differentCandidateDoesNotEraseHistoricalSource ()

discoveryFailureDoesNotEraseHistoricalSource :
  DiscoveryFailureMeansHistoricalSourceAbsent → ⊥
discoveryFailureDoesNotEraseHistoricalSource ()

sameSourceIdentityDoesNotPayPropositionSupport :
  SameSourceIdentityPaysPropositionSupport → ⊥
sameSourceIdentityDoesNotPayPropositionSupport ()

sameSourceIdentityDoesNotCreateAuthority :
  SameSourceIdentityCreatesAuthority → ⊥
sameSourceIdentityDoesNotCreateAuthority ()

record NatSourceDiscoveryBoundary : Set where
  constructor nat-source-discovery-boundary
  field
    failedLocatorMayScheduleDiscovery : Bool
    discoveryProviderIsSemanticallyPrivileged : Bool
    discoveryCandidatePaysSameSourceIdentity : Bool
    providerRankPaysSourceSupport : Bool
    providerSnippetPaysSourceSupport : Bool
    sameSourceIdentityRequiresSeparateReceipt : Bool
    sameSourceIdentityMapsPositive : Bool
    differentSourceMapsNegative : Bool
    unresolvedIdentityMapsZero : Bool
    differentCandidateMeansSourceAbsent : Bool
    discoveryFailureMeansSourceAbsent : Bool
    sameSourceIdentityPaysSourceSupport : Bool
    sameSourceIdentityCreatesAuthority : Bool
    admittedAlternateLocatorMayReenterExistingFetch : Bool

canonicalNatSourceDiscoveryBoundary : NatSourceDiscoveryBoundary
canonicalNatSourceDiscoveryBoundary =
  nat-source-discovery-boundary
    true false false false false true true true true false false false false true
