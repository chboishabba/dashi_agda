module DASHI.Moonshine.Monster3BMultiplicitySchurCoordinatesLeanReceiptValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Moonshine.Monster3BMultiplicitySchurCoordinatesLeanReceiptExact as Receipt

schurCompilerPinned :
  Receipt.genericSchurCoordinateCompilerSourceWritten Receipt.canonicalBoundary ≡ true
schurCompilerPinned = refl

ninetyCoordinatesPinned :
  Receipt.ninetyCoordinateSpecializationSourceWritten Receipt.canonicalBoundary ≡ true
ninetyCoordinatesPinned = refl

evaluationRecoveryPinned :
  Receipt.coordinateEvaluationRecoverySourceWritten Receipt.canonicalBoundary ≡ true
evaluationRecoveryPinned = refl

noMonsterAttachmentPromotion :
  Receipt.actualMonsterHZetaAttachmentPaidByReceipt Receipt.canonicalBoundary ≡ false
noMonsterAttachmentPromotion = refl

noSuzukiActionPromotion :
  Receipt.actualSuzukiActionPaidByReceipt Receipt.canonicalBoundary ≡ false
noSuzukiActionPromotion = refl

noTensorPromotion :
  Receipt.tensorEvaluationEquivalencePaidByReceipt Receipt.canonicalBoundary ≡ false
noTensorPromotion = refl
