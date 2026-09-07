module DASHI.Law.SensibLawOfficialHCALiveAcquisitionReceipt9c3007Exact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- Observed bounded official-HCA acquisition receipt.
--
-- This owner pins what the retained runtime receipt and acquired artifact show.
-- It deliberately separates that observation from a stronger claim that the
-- live process was executed from a clean working tree exactly matching the
-- embedded git head.  The receipt embeds 9c3007..., while the later locally
-- certified repair head is bb6de85....  The governed provider runtime source
-- itself did not change across that one-commit lineage, but exact-current-head
-- live execution remains a distinct receipt.
------------------------------------------------------------------------

rustRepository : String
rustRepository = "chboishabba/slr"

rustBranch : String
rustBranch = "agent/governed-online-r6-v2"

receiptRuntimeHead : String
receiptRuntimeHead = "9c3007be97f7e4a1e9a8bc9c7c85b92368515935"

locallyValidatedRepairHead : String
locallyValidatedRepairHead = "bb6de859ca82700cba70d2784f11c39a2c4c1826"

receiptSchema : String
receiptSchema = "sl.governed_legal_acquisition.v0_1"

receiptAuthority : String
receiptAuthority = "experimental_candidate_only"

providerName : String
providerName = "HighCourtAustralia"

providerAccessStatus : String
providerAccessStatus = "Available"

sourceIdentityRef : String
sourceIdentityRef = "case:[2026]-HCA-19"

propositionRef : String
propositionRef = "prop:cullen-positive-operational-duty"

mediumNeutralCitation : String
mediumNeutralCitation = "[2026] HCA 19"

explicitReference : String
explicitReference =
  "https://www.hcourt.gov.au/cases-and-judgments/judgments/judgments-1998-current/cullen-v-new-south-wales"

authorityBytesDigest : String
authorityBytesDigest =
  "sha256:5959632dbf3d88c3ddd96addb200dacdccf9d4aaf56cdccfacd8ca2b92cda991"

sourceRevisionRef : String
sourceRevisionRef =
  "source-revision:sha256:5959632dbf3d88c3ddd96addb200dacdccf9d4aaf56cdccfacd8ca2b92cda991"

record ObservedOfficialHCALiveReceipt : Set where
  constructor observedOfficialHCALiveReceipt
  field
    firstRunNetworkRequests : Nat
    firstRunNetworkRequestsIsOne : firstRunNetworkRequests ≡ 1

    firstRunLocallyIngested : Bool
    firstRunLocallyIngestedIsTrue : firstRunLocallyIngested ≡ true

    replayRunNetworkRequests : Nat
    replayRunNetworkRequestsIsZero : replayRunNetworkRequests ≡ 0

    replayResolvedPersisted : Bool
    replayResolvedPersistedIsTrue : replayResolvedPersisted ≡ true

    acquiredArtifactDigestMatchesReceipt : Bool
    acquiredArtifactDigestMatchesReceiptIsTrue :
      acquiredArtifactDigestMatchesReceipt ≡ true

    searchClaimedSemanticPayment : Bool
    searchClaimedSemanticPaymentIsFalse : searchClaimedSemanticPayment ≡ false

    acquisitionClaimedAuthorityReceipt : Bool
    acquisitionClaimedAuthorityReceiptIsFalse :
      acquisitionClaimedAuthorityReceipt ≡ false

    providerRuntimeSourceChangedBetweenReceiptAndRepairHead : Bool
    providerRuntimeSourceChangedBetweenReceiptAndRepairHeadIsFalse :
      providerRuntimeSourceChangedBetweenReceiptAndRepairHead ≡ false

    exactCleanWorkingTreeProducerProven : Bool
    exactCleanWorkingTreeProducerProvenIsFalse :
      exactCleanWorkingTreeProducerProven ≡ false

    exactRepairHeadLiveExecutionValidated : Bool
    exactRepairHeadLiveExecutionValidatedIsFalse :
      exactRepairHeadLiveExecutionValidated ≡ false

canonicalObservedOfficialHCALiveReceipt : ObservedOfficialHCALiveReceipt
canonicalObservedOfficialHCALiveReceipt =
  observedOfficialHCALiveReceipt
    1 refl
    true refl
    0 refl
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl

------------------------------------------------------------------------
-- Receipt-level firewalls.
------------------------------------------------------------------------

data LiveFetchAutomaticallySemanticPayment : Set where
data LiveFetchAutomaticallyLegalAuthority : Set where
data ArtifactDigestAutomaticallyPropositionCorrespondence : Set where
data EmbeddedGitHeadAutomaticallyCleanProducer : Set where
data ProviderSourceLineageAutomaticallyByteIdenticalBuild : Set where
\liveFetchDoesNotBecomeSemanticPayment :
  LiveFetchAutomaticallySemanticPayment → ⊥
liveFetchDoesNotBecomeSemanticPayment ()

liveFetchDoesNotBecomeLegalAuthority :
  LiveFetchAutomaticallyLegalAuthority → ⊥
liveFetchDoesNotBecomeLegalAuthority ()

artifactDigestDoesNotBecomePropositionCorrespondence :
  ArtifactDigestAutomaticallyPropositionCorrespondence → ⊥
artifactDigestDoesNotBecomePropositionCorrespondence ()

embeddedGitHeadDoesNotProveCleanProducer :
  EmbeddedGitHeadAutomaticallyCleanProducer → ⊥
embeddedGitHeadDoesNotProveCleanProducer ()

providerSourceLineageDoesNotProveByteIdenticalBuild :
  ProviderSourceLineageAutomaticallyByteIdenticalBuild → ⊥
providerSourceLineageDoesNotProveByteIdenticalBuild ()
