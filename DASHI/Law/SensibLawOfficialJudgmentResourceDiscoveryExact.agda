module DASHI.Law.SensibLawOfficialJudgmentResourceDiscoveryExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- Rust-led parity for the post-landing official-judgment acquisition seam.
--
-- The HCA landing page is already a locally persisted source revision.  Resource
-- discovery consumes those local bytes only, yielding typed DOCX/PDF references.
-- DOCX is preferred for downstream text/PNF work.  The full-document live fetch
-- is a separate one-request experiment and is not claimed as validated here.
------------------------------------------------------------------------

rustRepository : String
rustRepository = "chboishabba/slr"

rustBranch : String
rustBranch = "agent/governed-online-r6-v2"

rustSourceHead : String
rustSourceHead = "f4e0d4ac1a3611c001b6d91510a40071a9428835"

priorLocallyValidatedHead : String
priorLocallyValidatedHead = "bb6de859ca82700cba70d2784f11c39a2c4c1826"

resourceDiscoverySchema : String
resourceDiscoverySchema = "sl.official_judgment_resource_discovery.v0_1"

judgmentAcquisitionSchema : String
judgmentAcquisitionSchema = "sl.governed_official_judgment_acquisition.v0_1"

cullenMnc : String
cullenMnc = "[2026] HCA 19"

preferredDocumentKind : String
preferredDocumentKind = "Docx"

record OfficialJudgmentResourceDiscoveryBoundary : Set where
  constructor officialJudgmentResourceDiscoveryBoundary
  field
    landingPageAlreadyLocal : Bool
    landingPageAlreadyLocalIsTrue : landingPageAlreadyLocal ≡ true

    landingPageDiscoveryNetworkRequests : Nat
    landingPageDiscoveryNetworkRequestsIsZero : landingPageDiscoveryNetworkRequests ≡ 0

    docxReferenceDiscovered : Bool
    docxReferenceDiscoveredIsTrue : docxReferenceDiscovered ≡ true

    pdfReferenceDiscovered : Bool
    pdfReferenceDiscoveredIsTrue : pdfReferenceDiscovered ≡ true

    docxPreferredForDownstreamText : Bool
    docxPreferredForDownstreamTextIsTrue : docxPreferredForDownstreamText ≡ true

    resourceDiscoveryCandidateOnly : Bool
    resourceDiscoveryCandidateOnlyIsTrue : resourceDiscoveryCandidateOnly ≡ true

    resourceDiscoveryAutomaticallySemanticPayment : Bool
    resourceDiscoveryAutomaticallySemanticPaymentIsFalse :
      resourceDiscoveryAutomaticallySemanticPayment ≡ false

    resourceDiscoveryAutomaticallyLegalAuthority : Bool
    resourceDiscoveryAutomaticallyLegalAuthorityIsFalse :
      resourceDiscoveryAutomaticallyLegalAuthority ≡ false

    fullJudgmentFetchMaximumNetworkRequests : Nat
    fullJudgmentFetchMaximumNetworkRequestsIsOne :
      fullJudgmentFetchMaximumNetworkRequests ≡ 1

    fullJudgmentFetchRequiresLocalIngestion : Bool
    fullJudgmentFetchRequiresLocalIngestionIsTrue :
      fullJudgmentFetchRequiresLocalIngestion ≡ true

    fullJudgmentReplayNetworkRequests : Nat
    fullJudgmentReplayNetworkRequestsIsZero :
      fullJudgmentReplayNetworkRequests ≡ 0

    fullJudgmentLiveReceiptValidated : Bool
    fullJudgmentLiveReceiptValidatedIsFalse :
      fullJudgmentLiveReceiptValidated ≡ false

    currentRustHeadLocallyValidated : Bool
    currentRustHeadLocallyValidatedIsFalse :
      currentRustHeadLocallyValidated ≡ false

canonicalOfficialJudgmentResourceDiscoveryBoundary :
  OfficialJudgmentResourceDiscoveryBoundary
canonicalOfficialJudgmentResourceDiscoveryBoundary =
  officialJudgmentResourceDiscoveryBoundary
    true refl
    0 refl
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
    1 refl
    true refl
    0 refl
    false refl
    false refl

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data LandingResourceReferenceAutomaticallyHolding : Set where
data PreferredDocxAutomaticallyPropositionCorrespondence : Set where
data FullJudgmentBytesAutomaticallyRatio : Set where
data FullJudgmentBytesAutomaticallyCurrentAuthority : Set where

landingResourceReferenceDoesNotBecomeHolding :
  LandingResourceReferenceAutomaticallyHolding → ⊥
landingResourceReferenceDoesNotBecomeHolding ()

preferredDocxDoesNotBecomePropositionCorrespondence :
  PreferredDocxAutomaticallyPropositionCorrespondence → ⊥
preferredDocxDoesNotBecomePropositionCorrespondence ()

fullJudgmentBytesDoNotBecomeRatio :
  FullJudgmentBytesAutomaticallyRatio → ⊥
fullJudgmentBytesDoNotBecomeRatio ()

fullJudgmentBytesDoNotBecomeCurrentAuthority :
  FullJudgmentBytesAutomaticallyCurrentAuthority → ⊥
fullJudgmentBytesDoNotBecomeCurrentAuthority ()
