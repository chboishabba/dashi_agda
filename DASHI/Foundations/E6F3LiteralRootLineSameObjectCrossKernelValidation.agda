module DASHI.Foundations.E6F3LiteralRootLineSameObjectCrossKernelValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Foundations.E6F3LiteralRootLineSameObjectCrossKernelReceiptExact as Receipt

rootLineCountPinned : Receipt.literalRootLineCount Receipt.canonicalReceipt ≡ 36
rootLineCountPinned = refl

degreePinned : Receipt.degree Receipt.canonicalReceipt ≡ 15
degreePinned = refl

commonPinned : Receipt.commonNeighborCount Receipt.canonicalReceipt ≡ 6
commonPinned = refl

sameObjectSourceWritten :
  Receipt.literalRootLineQTwoEquivalenceLeanSourceWritten Receipt.canonicalBoundary ≡ true
sameObjectSourceWritten = refl

cartanDotSourceWritten :
  Receipt.cartanDotIntertwiningLeanSourceWritten Receipt.canonicalBoundary ≡ true
cartanDotSourceWritten = refl

leanKernelPending :
  Receipt.leanExactHeadKernelReceiptObserved Receipt.canonicalBoundary ≡ false
leanKernelPending = refl

noCardinalityPromotion :
  Receipt.cardinalityAlonePromotesSameObject Receipt.canonicalBoundary ≡ false
noCardinalityPromotion = refl
