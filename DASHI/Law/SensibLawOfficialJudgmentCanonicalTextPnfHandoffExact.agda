module DASHI.Law.SensibLawOfficialJudgmentCanonicalTextPnfHandoffExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- Rust-led parity for the canonical official-judgment text -> existing PNF ABI.
--
-- No new PNF subsystem is introduced.  The runtime reuses the existing
-- EvidentialBridgeReceipt contract, preserving document/text identity while
-- deferring world resolution and requiring semantic correspondence review.
------------------------------------------------------------------------

rustRepository : String
rustRepository = "chboishabba/slr"

rustBranch : String
rustBranch = "agent/governed-online-r6-v2"

rustSourceHead : String
rustSourceHead = "fa4ee80badc5e21a2b901b51d678b4791f499e51"

parserContractRef : String
parserContractRef = "sl.official_judgment.canonical_text.v0_1"

numericPnfCompilerContractRef : String
numericPnfCompilerContractRef = "sl.numeric_pnf_compiler.v0_1"

record CanonicalJudgmentPnfHandoffBoundary : Set where
  constructor canonicalJudgmentPnfHandoffBoundary
  field
    reusesExistingEvidentialBridge : Bool
    reusesExistingEvidentialBridgeIsTrue : reusesExistingEvidentialBridge ≡ true

    documentIdentityRetained : Bool
    documentIdentityRetainedIsTrue : documentIdentityRetained ≡ true

    canonicalTextDigestRetained : Bool
    canonicalTextDigestRetainedIsTrue : canonicalTextDigestRetained ≡ true

    residualDemandIdentityRetained : Bool
    residualDemandIdentityRetainedIsTrue : residualDemandIdentityRetained ≡ true

    worldResolutionDeferred : Bool
    worldResolutionDeferredIsTrue : worldResolutionDeferred ≡ true

    crossDocumentIdentityClosed : Bool
    crossDocumentIdentityClosedIsFalse : crossDocumentIdentityClosed ≡ false

    parserObservationSemanticAuthority : Bool
    parserObservationSemanticAuthorityIsFalse :
      parserObservationSemanticAuthority ≡ false

    semanticCorrespondenceRequired : Bool
    semanticCorrespondenceRequiredIsTrue : semanticCorrespondenceRequired ≡ true

    canonicalTextBridgeAutomaticallyWorldTruth : Bool
    canonicalTextBridgeAutomaticallyWorldTruthIsFalse :
      canonicalTextBridgeAutomaticallyWorldTruth ≡ false

    canonicalTextBridgeAutomaticallyLegalHolding : Bool
    canonicalTextBridgeAutomaticallyLegalHoldingIsFalse :
      canonicalTextBridgeAutomaticallyLegalHolding ≡ false

    currentRustHeadLocallyValidated : Bool
    currentRustHeadLocallyValidatedIsFalse : currentRustHeadLocallyValidated ≡ false

canonicalCanonicalJudgmentPnfHandoffBoundary : CanonicalJudgmentPnfHandoffBoundary
canonicalCanonicalJudgmentPnfHandoffBoundary =
  canonicalJudgmentPnfHandoffBoundary
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
    true refl
    false refl
    false refl
    false refl

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data PnfBridgeAutomaticallyCorrespondence : Set where
data PnfBridgeAutomaticallyWorldTruth : Set where
data PnfBridgeAutomaticallyHolding : Set where

pnfBridgeDoesNotBecomeCorrespondence :
  PnfBridgeAutomaticallyCorrespondence → ⊥
pnfBridgeDoesNotBecomeCorrespondence ()

pnfBridgeDoesNotBecomeWorldTruth :
  PnfBridgeAutomaticallyWorldTruth → ⊥
pnfBridgeDoesNotBecomeWorldTruth ()

pnfBridgeDoesNotBecomeHolding :
  PnfBridgeAutomaticallyHolding → ⊥
pnfBridgeDoesNotBecomeHolding ()
