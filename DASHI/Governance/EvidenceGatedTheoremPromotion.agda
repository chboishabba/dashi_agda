module DASHI.Governance.EvidenceGatedTheoremPromotion where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

open import Verification.JacobianCounterexampleKernel as Kernel
  using
    ( KernelCounterexampleReceipt
    ; kernelCounterexampleReceipt
    ; jacobianConjectureDimension3False
    )

------------------------------------------------------------------------
-- Fail-closed governance is a staging discipline, not a permanent embargo on
-- surprising conclusions.

data PromotionStage : Set where
  proposed : PromotionStage
  executableChecked : PromotionStage
  kernelChecked : PromotionStage
  consequencePromoted : PromotionStage

record PromotionEvidence : Set where
  constructor promotionEvidence
  field
    formulaFixed : Bool
    externalExactRegression : Bool
    provenanceRecorded : Bool
    kernelCollisionProof : Bool
    kernelJacobianIdentity : Bool
    logicalConsequenceKernelChecked : Bool

eligibleForCounterexamplePromotion : PromotionEvidence → Bool
eligibleForCounterexamplePromotion evidence with
  PromotionEvidence.formulaFixed evidence |
  PromotionEvidence.externalExactRegression evidence |
  PromotionEvidence.provenanceRecorded evidence |
  PromotionEvidence.kernelCollisionProof evidence |
  PromotionEvidence.kernelJacobianIdentity evidence |
  PromotionEvidence.logicalConsequenceKernelChecked evidence
... | true | true | true | true | true | true = true
... | _ | _ | _ | _ | _ | _ = false

alpogePromotionEvidence : PromotionEvidence
alpogePromotionEvidence =
  promotionEvidence true true true true true true

alpogeEligible :
  eligibleForCounterexamplePromotion alpogePromotionEvidence ≡ true
alpogeEligible = refl

record PromotionReceipt : Set where
  constructor promotionReceipt
  field
    initialFailClosedBoundaryRetained : Bool
    explicitPromotionPathProvided : Bool
    externalCheckDistinguishedFromKernelProof : Bool
    kernelCounterexampleReceiptIncluded : KernelCounterexampleReceipt
    dimensionThreeRefutationAvailable : Set
    surprisingResultPermanentlyBlocked : Bool
    surprisingResultPermanentlyBlockedIsFalse :
      surprisingResultPermanentlyBlocked ≡ false
    interpretation : String

promotionReceipt : PromotionReceipt
promotionReceipt =
  promotionReceipt
    true
    true
    true
    kernelCounterexampleReceipt
    (Kernel.¬ Kernel.JacobianConjectureDimension3)
    false
    refl
    "claims begin fail-closed, but a fixed formula, exact regression, provenance, kernel algebra and kernel logical consequence provide an explicit route to promotion"
