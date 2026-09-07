module DASHI.Law.SensibLawPreferredAustralianAuthorityAcquisitionExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- Parity owner for the Rust-led Australian acquisition/failover tranche.
--
-- The runtime implementation leads.  This module mirrors the implemented
-- acquisition order and its authority firewalls; it does not claim that the
-- first real official-source live receipt has already been produced.
------------------------------------------------------------------------

rustRepository : String
rustRepository = "chboishabba/slr"

rustBranch : String
rustBranch = "agent/governed-online-r6-v2"

rustSourceHead : String
rustSourceHead = "cbbf323e8a882a41b8aae46c5fb4e44874a919d4"

------------------------------------------------------------------------
-- Preferred acquisition order.
------------------------------------------------------------------------

data AcquisitionLane : Set where
  persistedLocal : AcquisitionLane
  installedOalc : AcquisitionLane
  officialCourt : AcquisitionLane
  sanctionedSpecialist : AcquisitionLane
  unresolved : AcquisitionLane

infix 4 _≺_
data _≺_ : AcquisitionLane → AcquisitionLane → Set where
  persisted≺oalc : persistedLocal ≺ installedOalc
  oalc≺official : installedOalc ≺ officialCourt
  official≺specialist : officialCourt ≺ sanctionedSpecialist
  specialist≺unresolved : sanctionedSpecialist ≺ unresolved

preferredPersistedBeforeOalc : persistedLocal ≺ installedOalc
preferredPersistedBeforeOalc = persisted≺oalc

preferredOalcBeforeOfficial : installedOalc ≺ officialCourt
preferredOalcBeforeOfficial = oalc≺official

preferredOfficialBeforeSpecialist : officialCourt ≺ sanctionedSpecialist
preferredOfficialBeforeSpecialist = official≺specialist

preferredSpecialistBeforeUnresolved : sanctionedSpecialist ≺ unresolved
preferredSpecialistBeforeUnresolved = specialist≺unresolved

------------------------------------------------------------------------
-- Provider-access states are acquisition coordinates only.
------------------------------------------------------------------------

data ProviderAccessStatus : Set where
  available : ProviderAccessStatus
  policyBlocked : ProviderAccessStatus
  tlsInvalid : ProviderAccessStatus
  temporarilyUnavailable : ProviderAccessStatus
  authorisationRequired : ProviderAccessStatus
  notConfigured : ProviderAccessStatus

record ProviderFailureCalibration : Set where
  constructor providerFailureCalibration
  field
    austlii403Status : ProviderAccessStatus
    jadeTlsStatus : ProviderAccessStatus
    providerFailureCountsAsNegativeLegalEvidence : Bool
    providerFailureCountsAsNegativeLegalEvidenceIsFalse :
      providerFailureCountsAsNegativeLegalEvidence ≡ false

canonicalProviderFailureCalibration : ProviderFailureCalibration
canonicalProviderFailureCalibration =
  providerFailureCalibration policyBlocked tlsInvalid false refl

------------------------------------------------------------------------
-- OALC is a revision-bound zero-network corpus lane.
------------------------------------------------------------------------

record OalcExactMncBoundary : Set where
  constructor oalcExactMncBoundary
  field
    corpusRevisionRetained : Bool
    corpusRevisionRetainedIsTrue : corpusRevisionRetained ≡ true
    sourceVersionRetained : Bool
    sourceVersionRetainedIsTrue : sourceVersionRetained ≡ true
    canonicalTextDigestRetained : Bool
    canonicalTextDigestRetainedIsTrue : canonicalTextDigestRetained ≡ true
    exactMncIndexed : Bool
    exactMncIndexedIsTrue : exactMncIndexed ≡ true
    fullCorpusTextRequiredInMemory : Bool
    fullCorpusTextRequiredInMemoryIsFalse : fullCorpusTextRequiredInMemory ≡ false
    lookupNetworkRequests : Nat
    lookupNetworkRequestsIsZero : lookupNetworkRequests ≡ 0
    lookupReceiptCandidateOnly : Bool
    lookupReceiptCandidateOnlyIsTrue : lookupReceiptCandidateOnly ≡ true

canonicalOalcExactMncBoundary : OalcExactMncBoundary
canonicalOalcExactMncBoundary =
  oalcExactMncBoundary
    true refl
    true refl
    true refl
    true refl
    false refl
    0 refl
    true refl

------------------------------------------------------------------------
-- Official Australian court providers are distinct provenance lanes.
------------------------------------------------------------------------

cullenMnc : String
cullenMnc = "[2026] HCA 19"

pabaiMnc : String
pabaiMnc = "[2025] FCA 796"

cullenOfficialProvider : String
cullenOfficialProvider = "HighCourtAustralia"

pabaiOfficialProvider : String
pabaiOfficialProvider = "FederalCourtAustralia"

record OfficialCourtAcquisitionBoundary : Set where
  constructor officialCourtAcquisitionBoundary
  field
    hcaFirstClassProvider : Bool
    hcaFirstClassProviderIsTrue : hcaFirstClassProvider ≡ true
    fcaFirstClassProvider : Bool
    fcaFirstClassProviderIsTrue : fcaFirstClassProvider ≡ true
    searchReturnsReferences : Bool
    searchReturnsReferencesIsTrue : searchReturnsReferences ≡ true
    fetchReturnsBytes : Bool
    fetchReturnsBytesIsTrue : fetchReturnsBytes ≡ true
    fetchRequiresLocalIngestionBeforePNF : Bool
    fetchRequiresLocalIngestionBeforePNFIsTrue :
      fetchRequiresLocalIngestionBeforePNF ≡ true
    firstOfficialFetchNetworkRequests : Nat
    firstOfficialFetchNetworkRequestsIsOne : firstOfficialFetchNetworkRequests ≡ 1
    sameDemandReplayNetworkRequests : Nat
    sameDemandReplayNetworkRequestsIsZero : sameDemandReplayNetworkRequests ≡ 0
    acquiredBytesRetainSHA256 : Bool
    acquiredBytesRetainSHA256IsTrue : acquiredBytesRetainSHA256 ≡ true
    boundedOfficialLiveReceiptValidated : Bool
    boundedOfficialLiveReceiptValidatedIsFalse : boundedOfficialLiveReceiptValidated ≡ false

canonicalOfficialCourtAcquisitionBoundary : OfficialCourtAcquisitionBoundary
canonicalOfficialCourtAcquisitionBoundary =
  officialCourtAcquisitionBoundary
    true refl
    true refl
    true refl
    true refl
    true refl
    1 refl
    0 refl
    true refl
    false refl

------------------------------------------------------------------------
-- Aggregator/specialist providers remain optional and sanctioned.
------------------------------------------------------------------------

record OptionalSpecialistBoundary : Set where
  constructor optionalSpecialistBoundary
  field
    austliiMandatoryForResearch : Bool
    austliiMandatoryForResearchIsFalse : austliiMandatoryForResearch ≡ false
    jadeMandatoryForResearch : Bool
    jadeMandatoryForResearchIsFalse : jadeMandatoryForResearch ≡ false
    austliiPublicModeReferenceOnly : Bool
    austliiPublicModeReferenceOnlyIsTrue : austliiPublicModeReferenceOnly ≡ true
    sanctionedAccessMayBeSeparate : Bool
    sanctionedAccessMayBeSeparateIsTrue : sanctionedAccessMayBeSeparate ≡ true

canonicalOptionalSpecialistBoundary : OptionalSpecialistBoundary
canonicalOptionalSpecialistBoundary =
  optionalSpecialistBoundary
    false refl
    false refl
    true refl
    true refl

------------------------------------------------------------------------
-- Fail-closed semantic firewalls.
------------------------------------------------------------------------

data ProviderFailureAutomaticallyPropositionFalse : Set where
data OalcHitAutomaticallyBindingAuthority : Set where
data OfficialCourtBytesAutomaticallyPropositionCorrespondence : Set where
data SameMncAutomaticallySameSourceRevision : Set where
data SuccessfulOfficialFetchAutomaticallyProductionReady : Set where

providerFailureDoesNotMakePropositionFalse :
  ProviderFailureAutomaticallyPropositionFalse → ⊥
providerFailureDoesNotMakePropositionFalse ()

oalcHitDoesNotBecomeBindingAuthority :
  OalcHitAutomaticallyBindingAuthority → ⊥
oalcHitDoesNotBecomeBindingAuthority ()

officialCourtBytesDoNotBecomePropositionCorrespondence :
  OfficialCourtBytesAutomaticallyPropositionCorrespondence → ⊥
officialCourtBytesDoNotBecomePropositionCorrespondence ()

sameMncDoesNotCollapseSourceRevisions :
  SameMncAutomaticallySameSourceRevision → ⊥
sameMncDoesNotCollapseSourceRevisions ()

successfulOfficialFetchDoesNotBecomeProductionReady :
  SuccessfulOfficialFetchAutomaticallyProductionReady → ⊥
successfulOfficialFetchDoesNotBecomeProductionReady ()
