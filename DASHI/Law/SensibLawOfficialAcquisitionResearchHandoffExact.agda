module DASHI.Law.SensibLawOfficialAcquisitionResearchHandoffExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- Rust-led parity owner for the R7 acquisition return path.
--
-- A provider receipt may rejoin the research engine only after local ingestion.
-- It becomes an immutable source revision input to the existing PNF/reasoning/
-- frontier machinery; it does not gain a second online semantic authority layer.
------------------------------------------------------------------------

rustRepository : String
rustRepository = "chboishabba/slr"

rustBranch : String
rustBranch = "agent/governed-online-r6-v2"

rustSourceHead : String
rustSourceHead = "9c3007be97f7e4a1e9a8bc9c7c85b92368515935"

record OfficialAcquisitionResearchHandoffBoundary : Set where
  constructor officialAcquisitionResearchHandoffBoundary
  field
    providerReceiptMustBeLocallyIngested : Bool
    providerReceiptMustBeLocallyIngestedIsTrue :
      providerReceiptMustBeLocallyIngested ≡ true

    acquisitionReceiptMustRemainCandidateOnly : Bool
    acquisitionReceiptMustRemainCandidateOnlyIsTrue :
      acquisitionReceiptMustRemainCandidateOnly ≡ true

    locallyIngestedAuthorityBecomesImmutableSourceRevision : Bool
    locallyIngestedAuthorityBecomesImmutableSourceRevisionIsTrue :
      locallyIngestedAuthorityBecomesImmutableSourceRevision ≡ true

    providerBytesDigestRetained : Bool
    providerBytesDigestRetainedIsTrue : providerBytesDigestRetained ≡ true

    parsedPnfIdentityRemainsSeparate : Bool
    parsedPnfIdentityRemainsSeparateIsTrue : parsedPnfIdentityRemainsSeparate ≡ true

    citationTopologyIdentityRemainsSeparate : Bool
    citationTopologyIdentityRemainsSeparateIsTrue :
      citationTopologyIdentityRemainsSeparate ≡ true

    acquiredSourceMayFeedNormalReasoningDelta : Bool
    acquiredSourceMayFeedNormalReasoningDeltaIsTrue :
      acquiredSourceMayFeedNormalReasoningDelta ≡ true

    reasoningDeltaMayEnrichQueryVocabulary : Bool
    reasoningDeltaMayEnrichQueryVocabularyIsTrue :
      reasoningDeltaMayEnrichQueryVocabulary ≡ true

    reasoningDeltaMayEnrichAuthorityNeighbourhood : Bool
    reasoningDeltaMayEnrichAuthorityNeighbourhoodIsTrue :
      reasoningDeltaMayEnrichAuthorityNeighbourhood ≡ true

    acquiredSourceMayNarrowExistingResidual : Bool
    acquiredSourceMayNarrowExistingResidualIsTrue :
      acquiredSourceMayNarrowExistingResidual ≡ true

    firstAcquisitionNetworkRequests : Nat
    firstAcquisitionNetworkRequestsIsOne : firstAcquisitionNetworkRequests ≡ 1

    sameDemandPersistedReplayNetworkRequests : Nat
    sameDemandPersistedReplayNetworkRequestsIsZero :
      sameDemandPersistedReplayNetworkRequests ≡ 0

    acquisitionHandoffAutomaticallySemanticPayment : Bool
    acquisitionHandoffAutomaticallySemanticPaymentIsFalse :
      acquisitionHandoffAutomaticallySemanticPayment ≡ false

    officialLiveReceiptAlreadyValidated : Bool
    officialLiveReceiptAlreadyValidatedIsFalse :
      officialLiveReceiptAlreadyValidated ≡ false

canonicalOfficialAcquisitionResearchHandoffBoundary :
  OfficialAcquisitionResearchHandoffBoundary
canonicalOfficialAcquisitionResearchHandoffBoundary =
  officialAcquisitionResearchHandoffBoundary
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    1 refl
    0 refl
    false refl
    false refl

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data AcquisitionHandoffAutomaticallyHolding : Set where
data AcquiredBytesAutomaticallyReasoningEdge : Set where
data ReasoningDeltaAutomaticallyRatio : Set where
data NarrowedResidualAutomaticallyProofClosed : Set where

acquisitionHandoffDoesNotBecomeHolding :
  AcquisitionHandoffAutomaticallyHolding → ⊥
acquisitionHandoffDoesNotBecomeHolding ()

acquiredBytesDoNotBecomeReasoningEdge :
  AcquiredBytesAutomaticallyReasoningEdge → ⊥
acquiredBytesDoNotBecomeReasoningEdge ()

reasoningDeltaDoesNotBecomeRatio :
  ReasoningDeltaAutomaticallyRatio → ⊥
reasoningDeltaDoesNotBecomeRatio ()

narrowedResidualDoesNotBecomeProofClosed :
  NarrowedResidualAutomaticallyProofClosed → ⊥
narrowedResidualDoesNotBecomeProofClosed ()
