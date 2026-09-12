module DASHI.Culture.BlochfieldHistoricalWalletReviewCandidateExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.SnowballOSINTAcquisitionInvariantExact as OSINT
import DASHI.Culture.BlochfieldCreatorGenealogySnowballExact as Creator

------------------------------------------------------------------------
-- BLOCHFIELD HISTORICAL WALLET-REVIEW IDENTITY CANDIDATE
--
-- A third-party extension-review mirror records a review under display name
-- "Yasmin Anacreto" dated 2024-05-08 for Fewcha Move Wallet.  The review text
-- describes creating a wallet and failures to connect/show/import it.
--
-- This is a useful pre-X web3/wallet chronology coordinate because it lies
-- between the 2024-03-31 same-name Medium candidate and the mirror-reported
-- November-2024 @msiyasmsi join date.  It remains identityUnresolved: the
-- review mirror does not expose a native account link, wallet address,
-- signature, authenticated profile, or cross-platform identity assertion.
------------------------------------------------------------------------

fewchaWalletReviewObservation : OSINT.OSINTObservation
fewchaWalletReviewObservation =
  OSINT.osint-observation
    "https://extpose.com/ext/ebfidpplhabeedpnhjnobghokpiioolj"
    ""
    "2026-09-12 search-indexed extension-review mirror"
    OSINT.tertiaryAggregation
    OSINT.identityUnresolved
    "reviewer display name Yasmin Anacreto appears on 2024-05-08 review of Fewcha Move Wallet describing wallet creation/connection/import failure"
    "historical same-name web3/wallet context only; does not establish @msiyasmsi identity, wallet ownership, authenticated account custody, endorsement, or Blochfield lineage"
    "no native review-platform identity digest or wallet-address receipt acquired"
    false
    true
    true

record HistoricalWalletReviewCandidate : Set where
  constructor historical-wallet-review-candidate
  field
    observation : OSINT.OSINTObservation
    reviewerDisplayName : String
    reviewDate : String
    reviewedProduct : String
    context : String
    predatesObservedXJoin : Bool
    predatesObservedXJoinIsTrue : predatesObservedXJoin ≡ true
    exactSamePersonIdentityPaid : Bool
    exactSamePersonIdentityPaidIsFalse : exactSamePersonIdentityPaid ≡ false
    walletOwnershipPaid : Bool
    walletOwnershipPaidIsFalse : walletOwnershipPaid ≡ false
    authenticatedReviewerProfilePaid : Bool
    authenticatedReviewerProfilePaidIsFalse :
      authenticatedReviewerProfilePaid ≡ false

open HistoricalWalletReviewCandidate public

historicalWalletReviewCandidate : HistoricalWalletReviewCandidate
historicalWalletReviewCandidate =
  historical-wallet-review-candidate
    fewchaWalletReviewObservation
    "Yasmin Anacreto"
    "2024-05-08"
    "Fewcha Move Wallet"
    "same-name pre-X web3/wallet usage-context candidate"
    true refl
    false refl
    false refl
    false refl

------------------------------------------------------------------------
-- Payment remains ordered and fail-closed.
------------------------------------------------------------------------

crossPlatformIdentityWeldStillUnpaid : Creator.GenealogyStanding
crossPlatformIdentityWeldStillUnpaid =
  Creator.genealogyStanding Creator.crossPlatformIdentityWeld

data SameNameWalletReviewPaysSamePerson : Set where
data WalletUseContextPaysAccountOwnership : Set where
data ReviewMirrorPaysNativeIdentity : Set where
data HistoricalWeb3ContinuityPaysBlochfieldLineage : Set where

sameNameWalletReviewDoesNotPaySamePerson :
  SameNameWalletReviewPaysSamePerson → ⊥
sameNameWalletReviewDoesNotPaySamePerson ()

walletUseContextDoesNotPayAccountOwnership :
  WalletUseContextPaysAccountOwnership → ⊥
walletUseContextDoesNotPayAccountOwnership ()

reviewMirrorDoesNotPayNativeIdentity : ReviewMirrorPaysNativeIdentity → ⊥
reviewMirrorDoesNotPayNativeIdentity ()

historicalWeb3ContinuityDoesNotPayBlochfieldLineage :
  HistoricalWeb3ContinuityPaysBlochfieldLineage → ⊥
historicalWeb3ContinuityDoesNotPayBlochfieldLineage ()

------------------------------------------------------------------------
-- Semantic checksum:
--
--   same name + dated wallet-use context
--     > same name alone for discovery priority
--
--   same name + dated wallet-use context
--     != authenticated same-person identity
--     != wallet-address ownership
--     != native account custody
--     != Blochfield ancestry
--
-- The next paying identity receipt remains a native mutual link, signed wallet
-- assertion, authenticated platform account link, or explicit creator statement.
------------------------------------------------------------------------
