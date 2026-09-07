module DASHI.Law.SensibLawOfficialHCAFullJudgmentLiveReceipt516867cExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- Observed full-judgment HCA materialization receipt.
--
-- The live execution is pinned to Rust head 516867c....  The later repair head
-- acd6a25... changes only the escaped-JSON source-contract checker; compare
-- audit shows no runtime/provider/materializer/review implementation change.
-- The complete retained JSON receipt now supplies both carrier and canonical-
-- text digests exactly, so no digest coordinate remains guessed or truncated.
------------------------------------------------------------------------

rustRepository : String
rustRepository = "chboishabba/slr"

rustBranch : String
rustBranch = "agent/governed-online-r6-v2"

receiptRuntimeHead : String
receiptRuntimeHead = "516867c503b33ea880419f9ca512307feec48e2b"

locallyValidatedRepairHead : String
locallyValidatedRepairHead = "acd6a254d484721c921177c4c72b222aa59ac172"

receiptSchema : String
receiptSchema = "sl.governed_official_judgment_acquisition.v0_1"

receiptAuthority : String
receiptAuthority = "experimental_candidate_only"

providerName : String
providerName = "HighCourtAustralia"

residualRef : String
residualRef = "residual:cullen-positive-operational-act"

propositionRef : String
propositionRef = "prop:cullen-positive-operational-duty"

scheduledProducerRef : String
scheduledProducerRef = "producer:exact-primary-authority"

hypothesisRef : String
hypothesisRef = "hyp:residual:cullen-positive-operational-act:support"

documentSourceIdentityRef : String
documentSourceIdentityRef = "document:hca:[2026]-HCA-19:docx"

documentBytesDigest : String
documentBytesDigest =
  "sha256:f171fcaa304de4e1a8be9b7e2a200a181025a81456fa89dec18516805cad15b9"

sourceRevisionRef : String
sourceRevisionRef =
  "source-revision:sha256:f171fcaa304de4e1a8be9b7e2a200a181025a81456fa89dec18516805cad15b9"

canonicalTextDigest : String
canonicalTextDigest =
  "sha256:53f4037cbb6a254634b43e5747bf398f44519a8eea1c9a904d146f7674564b5a"

record ObservedFullJudgmentLiveReceipt : Set where
  constructor observedFullJudgmentLiveReceipt
  field
    landingNetworkRequests : Nat
    landingNetworkRequestsIsZero : landingNetworkRequests ≡ 0

    resourceDiscoveryNetworkRequests : Nat
    resourceDiscoveryNetworkRequestsIsZero : resourceDiscoveryNetworkRequests ≡ 0

    documentNetworkRequests : Nat
    documentNetworkRequestsIsOne : documentNetworkRequests ≡ 1

    replayNetworkRequests : Nat
    replayNetworkRequestsIsZero : replayNetworkRequests ≡ 0

    canonicalParagraphCount : Nat
    canonicalParagraphCountIs202 : canonicalParagraphCount ≡ 202

    sourceRoutePaysScheduledGap : Bool
    sourceRoutePaysScheduledGapIsTrue : sourceRoutePaysScheduledGap ≡ true

    sourceRouteUsesScheduledProducer : Bool
    sourceRouteUsesScheduledProducerIsTrue : sourceRouteUsesScheduledProducer ≡ true

    documentLocallyIngested : Bool
    documentLocallyIngestedIsTrue : documentLocallyIngested ≡ true

    canonicalTextLocallyMaterialized : Bool
    canonicalTextLocallyMaterializedIsTrue : canonicalTextLocallyMaterialized ≡ true

    acquisitionClaimedSemanticPayment : Bool
    acquisitionClaimedSemanticPaymentIsFalse : acquisitionClaimedSemanticPayment ≡ false

    acquisitionClaimedLegalAuthority : Bool
    acquisitionClaimedLegalAuthorityIsFalse : acquisitionClaimedLegalAuthority ≡ false

    acquisitionClaimedConsumerClosure : Bool
    acquisitionClaimedConsumerClosureIsFalse : acquisitionClaimedConsumerClosure ≡ false

    exactDocumentDigestPinnedHere : Bool
    exactDocumentDigestPinnedHereIsTrue : exactDocumentDigestPinnedHere ≡ true

    exactCanonicalTextDigestPinnedHere : Bool
    exactCanonicalTextDigestPinnedHereIsTrue : exactCanonicalTextDigestPinnedHere ≡ true

    runtimeImplementationChangedBetweenReceiptAndRepairHead : Bool
    runtimeImplementationChangedBetweenReceiptAndRepairHeadIsFalse :
      runtimeImplementationChangedBetweenReceiptAndRepairHead ≡ false

    exactRepairHeadLiveExecutionValidated : Bool
    exactRepairHeadLiveExecutionValidatedIsFalse :
      exactRepairHeadLiveExecutionValidated ≡ false

canonicalObservedFullJudgmentLiveReceipt : ObservedFullJudgmentLiveReceipt
canonicalObservedFullJudgmentLiveReceipt =
  observedFullJudgmentLiveReceipt
    0 refl
    0 refl
    1 refl
    0 refl
    202 refl
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
    true refl
    true refl
    false refl
    false refl

------------------------------------------------------------------------
-- Receipt-level firewalls.
------------------------------------------------------------------------

data FullJudgmentFetchAutomaticallySemanticPayment : Set where
data CanonicalTextAutomaticallyPropositionCorrespondence : Set where
data CanonicalTextAutomaticallyRatio : Set where
data BoundSourceRouteAutomaticallyConsumerClosure : Set where
data ExactDigestAutomaticallySemanticAuthority : Set where

fullJudgmentFetchDoesNotBecomeSemanticPayment :
  FullJudgmentFetchAutomaticallySemanticPayment → ⊥
fullJudgmentFetchDoesNotBecomeSemanticPayment ()

canonicalTextDoesNotBecomePropositionCorrespondence :
  CanonicalTextAutomaticallyPropositionCorrespondence → ⊥
canonicalTextDoesNotBecomePropositionCorrespondence ()

canonicalTextDoesNotBecomeRatio : CanonicalTextAutomaticallyRatio → ⊥
canonicalTextDoesNotBecomeRatio ()

boundSourceRouteDoesNotCloseConsumer :
  BoundSourceRouteAutomaticallyConsumerClosure → ⊥
boundSourceRouteDoesNotCloseConsumer ()

exactDigestDoesNotBecomeSemanticAuthority :
  ExactDigestAutomaticallySemanticAuthority → ⊥
exactDigestDoesNotBecomeSemanticAuthority ()
