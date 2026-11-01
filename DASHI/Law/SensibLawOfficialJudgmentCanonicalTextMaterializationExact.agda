module DASHI.Law.SensibLawOfficialJudgmentCanonicalTextMaterializationExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- Rust-led parity for deterministic local DOCX -> canonical-text conversion.
--
-- The carrier transformation reads word/document.xml from locally acquired DOCX
-- bytes, preserves paragraph count, normalizes line endings, and emits a separate
-- canonical-text identity.  It is not a proposition parser or legal-authority
-- producer.  The current Rust source head still awaits local CI and the real HCA
-- DOCX fetch remains a separate explicit live receipt.
------------------------------------------------------------------------

rustRepository : String
rustRepository = "chboishabba/slr"

rustBranch : String
rustBranch = "agent/governed-online-r6-v2"

rustSourceHead : String
rustSourceHead = "4ffbd1bc66fd92ee1bde051685e4dad1c0c14d33"

priorValidatedRustHead : String
priorValidatedRustHead = "bb6de859ca82700cba70d2784f11c39a2c4c1826"

fullJudgmentReceiptSchema : String
fullJudgmentReceiptSchema = "sl.governed_official_judgment_acquisition.v0_1"

record CanonicalJudgmentTextBoundary : Set where
  constructor canonicalJudgmentTextBoundary
  field
    sourceCarrierIsDocx : Bool
    sourceCarrierIsDocxIsTrue : sourceCarrierIsDocx ≡ true

    documentXmlSelected : Bool
    documentXmlSelectedIsTrue : documentXmlSelected ≡ true

    materializationNetworkRequests : Nat
    materializationNetworkRequestsIsZero : materializationNetworkRequests ≡ 0

    bytesDigestRetainedSeparately : Bool
    bytesDigestRetainedSeparatelyIsTrue : bytesDigestRetainedSeparately ≡ true

    canonicalTextDigestRetainedSeparately : Bool
    canonicalTextDigestRetainedSeparatelyIsTrue :
      canonicalTextDigestRetainedSeparately ≡ true

    paragraphCountRetained : Bool
    paragraphCountRetainedIsTrue : paragraphCountRetained ≡ true

    lineEndingsNormalizedDeterministically : Bool
    lineEndingsNormalizedDeterministicallyIsTrue :
      lineEndingsNormalizedDeterministically ≡ true

    tabsAndExplicitBreaksRetained : Bool
    tabsAndExplicitBreaksRetainedIsTrue : tabsAndExplicitBreaksRetained ≡ true

    canonicalTextMayFeedPnf : Bool
    canonicalTextMayFeedPnfIsTrue : canonicalTextMayFeedPnf ≡ true

    materializationAutomaticallySemanticPayment : Bool
    materializationAutomaticallySemanticPaymentIsFalse :
      materializationAutomaticallySemanticPayment ≡ false

    materializationAutomaticallyLegalAuthority : Bool
    materializationAutomaticallyLegalAuthorityIsFalse :
      materializationAutomaticallyLegalAuthority ≡ false

    currentRustHeadLocallyValidated : Bool
    currentRustHeadLocallyValidatedIsFalse : currentRustHeadLocallyValidated ≡ false

    fullJudgmentLiveReceiptValidated : Bool
    fullJudgmentLiveReceiptValidatedIsFalse : fullJudgmentLiveReceiptValidated ≡ false

canonicalCanonicalJudgmentTextBoundary : CanonicalJudgmentTextBoundary
canonicalCanonicalJudgmentTextBoundary =
  canonicalJudgmentTextBoundary
    true refl
    true refl
    0 refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl

------------------------------------------------------------------------
-- Carrier/semantic firewalls.
------------------------------------------------------------------------

data CanonicalTextAutomaticallyProposition : Set where
data CanonicalTextAutomaticallyHolding : Set where
data CanonicalTextDigestAutomaticallySameAsBytesDigest : Set where
data ParagraphBoundaryAutomaticallyLegalReasoningBoundary : Set where

canonicalTextDoesNotBecomeProposition :
  CanonicalTextAutomaticallyProposition → ⊥
canonicalTextDoesNotBecomeProposition ()

canonicalTextDoesNotBecomeHolding :
  CanonicalTextAutomaticallyHolding → ⊥
canonicalTextDoesNotBecomeHolding ()

textDigestDoesNotCollapseIntoBytesDigest :
  CanonicalTextDigestAutomaticallySameAsBytesDigest → ⊥
textDigestDoesNotCollapseIntoBytesDigest ()

paragraphBoundaryDoesNotBecomeLegalReasoningBoundary :
  ParagraphBoundaryAutomaticallyLegalReasoningBoundary → ⊥
paragraphBoundaryDoesNotBecomeLegalReasoningBoundary ()
