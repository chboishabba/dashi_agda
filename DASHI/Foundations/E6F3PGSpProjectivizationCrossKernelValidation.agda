module DASHI.Foundations.E6F3PGSpProjectivizationCrossKernelValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Foundations.E6F3PGSpProjectivizationCrossKernelReceiptExact as Receipt

fourSpaceOrder : Receipt.fourSpaceGeneratedOrder Receipt.canonicalReceipt ≡ 103680
fourSpaceOrder = refl

kernelOrder : Receipt.exteriorSquareKernelOrder Receipt.canonicalReceipt ≡ 2
kernelOrder = refl

projectiveOrder : Receipt.projectiveQuotientOrder Receipt.canonicalReceipt ≡ 51840
projectiveOrder = refl

plusMinusKernelSourceWritten :
  Receipt.kernelExactlyPlusMinusIdentityLeanSourceWritten Receipt.canonicalBoundary ≡ true
plusMinusKernelSourceWritten = refl

abstractIsomorphismStillNotManufactured :
  Receipt.abstractPGSp4EqualsWE6Paid Receipt.canonicalBoundary ≡ false
abstractIsomorphismStillNotManufactured = refl
