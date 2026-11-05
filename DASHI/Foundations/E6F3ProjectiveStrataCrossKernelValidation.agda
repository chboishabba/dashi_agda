module DASHI.Foundations.E6F3ProjectiveStrataCrossKernelValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Foundations.E6F3ProjectiveStrataCrossKernelReceiptExact as Receipt

qZeroVerticesPinned : Receipt.vertices Receipt.qZeroReceipt ≡ 40
qZeroVerticesPinned = refl

qOneVerticesPinned : Receipt.vertices Receipt.qOneReceipt ≡ 45
qOneVerticesPinned = refl

qTwoVerticesPinned : Receipt.vertices Receipt.qTwoReceipt ≡ 36
qTwoVerticesPinned = refl

projectiveTotalPinned : Receipt.projectiveTotal ≡ 121
projectiveTotalPinned = refl

qOneSRGSourceWritten : Receipt.qOneSRGLeanSourceWritten Receipt.canonicalBoundary ≡ true
qOneSRGSourceWritten = refl

leanKernelPending : Receipt.leanExactHeadKernelReceiptObserved Receipt.canonicalBoundary ≡ false
leanKernelPending = refl

noQOneExceptionalPromotion :
  Receipt.qOneGraphPromotedToExceptionalRepresentation Receipt.canonicalBoundary ≡ false
noQOneExceptionalPromotion = refl
