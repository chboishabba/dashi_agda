module DASHI.Reasoning.SFMVerificationDependency where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Reasoning.SFMVerifiedClaimPresentation as SFM

------------------------------------------------------------------------
-- Proof-bearing verification adapters for SFM.
--
-- A receipt or card may be inhabited while unchecked, rejected or blocked.
-- Promotion therefore consumes an indexed checked-receipt witness, not the
-- existence of a receipt record or a targetVerified Boolean.
------------------------------------------------------------------------

record CheckedReceipt (receipt : SFM.VerificationReceipt) : Set where
  field
    statusIsKernelChecked :
      SFM.VerificationReceipt.status receipt ≡ SFM.kernelChecked
    placeholdersAbsent :
      SFM.VerificationReceipt.placeholdersAbsentClaimed receipt ≡ true
    checkedDependencyReceipt : String

open CheckedReceipt public

record CheckedTheoremCard
    (receipt : SFM.VerificationReceipt)
    (card : SFM.TheoremCard) : Set where
  field
    checkedReceipt : CheckedReceipt receipt
    faithfulCard : SFM.CardFaithfulness receipt card
    displayedStatusChecked :
      SFM.TheoremCard.verificationStatus card ≡ SFM.kernelChecked

open CheckedTheoremCard public

checkedCardStatusFromDependencies :
  ∀ {receipt card} →
  CheckedTheoremCard receipt card →
  SFM.TheoremCard.verificationStatus card ≡ SFM.kernelChecked
checkedCardStatusFromDependencies witness = displayedStatusChecked witness

record VerifiedMemeTranslation
    (translation : SFM.ProductiveMemeTranslation) : Set₁ where
  field
    targetReceipt : SFM.VerificationReceipt
    targetChecked : CheckedReceipt targetReceipt
    verificationRuleReceipt : String
    targetVerifiedProjection :
      SFM.ProductiveMemeTranslation.targetVerified translation ≡ true
    literalIdentityStillRejected :
      SFM.ProductiveMemeTranslation.literalIdentityClaimed translation ≡ false

open VerifiedMemeTranslation public

record SFMVerificationDependencyBoundary : Set where
  field
    receiptInhabitationEqualsKernelCheck : Bool
    theoremCardInhabitationEqualsFaithfulness : Bool
    checkedStatusRequiresEqualityWitness : Bool
    placeholdersRequireEqualityWitness : Bool
    targetVerifiedBooleanReconstructsReceipt : Bool
    literalIdentityRequiredForTranslation : Bool
    boundaryNote : String

canonicalSFMVerificationDependencyBoundary :
  SFMVerificationDependencyBoundary
canonicalSFMVerificationDependencyBoundary = record
  { receiptInhabitationEqualsKernelCheck = false
  ; theoremCardInhabitationEqualsFaithfulness = false
  ; checkedStatusRequiresEqualityWitness = true
  ; placeholdersRequireEqualityWitness = true
  ; targetVerifiedBooleanReconstructsReceipt = false
  ; literalIdentityRequiredForTranslation = false
  ; boundaryNote =
      "SFM promotion consumes a checked receipt and card-faithfulness witnesses. Record existence and Boolean projections remain insufficient."
  }
