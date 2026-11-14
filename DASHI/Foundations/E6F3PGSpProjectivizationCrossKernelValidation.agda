module DASHI.Foundations.E6F3PGSpProjectivizationCrossKernelValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Foundations.E6F3PGSpProjectivizationCrossKernelReceiptExact as Receipt

fourSpaceOrder : Receipt.fourSpaceGeneratedOrder Receipt.canonicalReceipt ≡ 103680
fourSpaceOrder = refl

kernelOrder : Receipt.exteriorSquareKernelOrder Receipt.canonicalReceipt ≡ 2
kernelOrder = refl

projectiveOrder : Receipt.projectiveQuotientOrder Receipt.canonicalReceipt ≡ 51840
projectiveOrder = refl

inducedFiveImageOrder : Receipt.inducedFiveSpaceImageOrder Receipt.canonicalReceipt ≡ 51840
inducedFiveImageOrder = refl

repoE6FiveImageOrder : Receipt.repoE6FiveSpaceImageOrder Receipt.canonicalReceipt ≡ 51840
repoE6FiveImageOrder = refl

plusMinusKernelSourceWritten :
  Receipt.kernelExactlyPlusMinusIdentityLeanSourceWritten Receipt.canonicalBoundary ≡ true
plusMinusKernelSourceWritten = refl

literalImageEqualitySourceWritten :
  Receipt.literalFiveSpaceMatrixImageEqualityLeanSourceWritten Receipt.canonicalBoundary ≡ true
literalImageEqualitySourceWritten = refl

sameActionRecognitionSourceWritten :
  Receipt.sameActionMatrixImageRecognitionLeanSourceWritten Receipt.canonicalBoundary ≡ true
sameActionRecognitionSourceWritten = refl

recognitionInterfaceInhabitedSourceWritten :
  Receipt.pgspWeylRecognitionInterfaceInhabitedAtMatrixImageLeanSourceWritten Receipt.canonicalBoundary ≡ true
recognitionInterfaceInhabitedSourceWritten = refl

leanKernelStillPending :
  Receipt.leanExactHeadKernelReceiptObserved Receipt.canonicalBoundary ≡ false
leanKernelStillPending = refl

abstractIsomorphismStillNotManufactured :
  Receipt.abstractPGSp4EqualsWE6Paid Receipt.canonicalBoundary ≡ false
abstractIsomorphismStillNotManufactured = refl
