module DASHI.Law.SensibLawGovernedOnlineR6ParityExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- Narrow parity owner for the Rust R6 governed-online execution tranche.
--
-- Rust is the implementation lead.  This file mirrors only contracts already
-- present on the Rust branch; it does not manufacture live execution or legal
-- authority.  The opt-in live receipt is not yet claimed as validated here.
------------------------------------------------------------------------

rustRepository : String
rustRepository = "chboishabba/slr"

rustBranch : String
rustBranch = "agent/governed-online-r6-v2"

rustSourceHead : String
rustSourceHead = "43c7eb9a1bcd73414607622de5c50e4463329c25"

liveReceiptSchema : String
liveReceiptSchema = "sl.governed_legal_acquisition.v0_1"

record GovernedOnlineR6Boundary : Set where
  constructor governedOnlineR6Boundary
  field
    knownAuthorityResolverImplemented : Bool
    knownAuthorityResolverImplementedIsTrue : knownAuthorityResolverImplemented ≡ true

    persistedResolutionPrecedesLive : Bool
    persistedResolutionPrecedesLiveIsTrue : persistedResolutionPrecedesLive ≡ true

    searchReturnsReferences : Bool
    searchReturnsReferencesIsTrue : searchReturnsReferences ≡ true

    fetchReturnsBytes : Bool
    fetchReturnsBytesIsTrue : fetchReturnsBytes ≡ true

    semanticsBeginAfterLocalIngestion : Bool
    semanticsBeginAfterLocalIngestionIsTrue : semanticsBeginAfterLocalIngestion ≡ true

    schedulerOwnsHTTP : Bool
    schedulerOwnsHTTPIsFalse : schedulerOwnsHTTP ≡ false

    liveNetworkFeatureGated : Bool
    liveNetworkFeatureGatedIsTrue : liveNetworkFeatureGated ≡ true

    explicitOperatorOptInRequired : Bool
    explicitOperatorOptInRequiredIsTrue : explicitOperatorOptInRequired ≡ true

    legalHostMinimumPacingSeconds : Nat
    legalHostMinimumPacingSecondsIsFour : legalHostMinimumPacingSeconds ≡ 4

    legalHostBurst : Nat
    legalHostBurstIsOne : legalHostBurst ≡ 1

    citationFollowMaxDepth : Nat
    citationFollowMaxDepthIsOne : citationFollowMaxDepth ≡ 1

    citationFollowMaxNewDocuments : Nat
    citationFollowMaxNewDocumentsIsFive : citationFollowMaxNewDocuments ≡ 5

    firstGovernedFetchNetworkRequests : Nat
    firstGovernedFetchNetworkRequestsIsOne : firstGovernedFetchNetworkRequests ≡ 1

    sameDemandReplayNetworkRequests : Nat
    sameDemandReplayNetworkRequestsIsZero : sameDemandReplayNetworkRequests ≡ 0

    acquiredBytesRetainSHA256Identity : Bool
    acquiredBytesRetainSHA256IdentityIsTrue : acquiredBytesRetainSHA256Identity ≡ true

    acquisitionReceiptCandidateOnly : Bool
    acquisitionReceiptCandidateOnlyIsTrue : acquisitionReceiptCandidateOnly ≡ true

    liveProviderImplementationPresent : Bool
    liveProviderImplementationPresentIsTrue : liveProviderImplementationPresent ≡ true

    boundedLiveProviderReceiptValidated : Bool
    boundedLiveProviderReceiptValidatedIsFalse : boundedLiveProviderReceiptValidated ≡ false

    localRustCIEqualsAgdaKernelCertification : Bool
    localRustCIEqualsAgdaKernelCertificationIsFalse :
      localRustCIEqualsAgdaKernelCertification ≡ false

canonicalGovernedOnlineR6Boundary : GovernedOnlineR6Boundary
canonicalGovernedOnlineR6Boundary =
  governedOnlineR6Boundary
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl
    true refl
    true refl
    4 refl
    1 refl
    1 refl
    5 refl
    1 refl
    0 refl
    true refl
    true refl
    true refl
    false refl
    false refl

------------------------------------------------------------------------
-- Authority firewalls.
------------------------------------------------------------------------

data SearchReferenceAutomaticallySemanticPayment : Set where
data FetchBytesAutomaticallyLegalAuthority : Set where
data LocalIngestionAutomaticallyPropositionCorrespondence : Set where
data SuccessfulLiveFetchAutomaticallyProductionReady : Set where

searchReferenceDoesNotBecomeSemanticPayment :
  SearchReferenceAutomaticallySemanticPayment → ⊥
searchReferenceDoesNotBecomeSemanticPayment ()

fetchBytesDoNotBecomeLegalAuthority :
  FetchBytesAutomaticallyLegalAuthority → ⊥
fetchBytesDoNotBecomeLegalAuthority ()

localIngestionDoesNotBecomePropositionCorrespondence :
  LocalIngestionAutomaticallyPropositionCorrespondence → ⊥
localIngestionDoesNotBecomePropositionCorrespondence ()

successfulLiveFetchDoesNotBecomeProductionReady :
  SuccessfulLiveFetchAutomaticallyProductionReady → ⊥
successfulLiveFetchDoesNotBecomeProductionReady ()
