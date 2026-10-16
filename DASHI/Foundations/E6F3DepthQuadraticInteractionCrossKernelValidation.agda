module DASHI.Foundations.E6F3DepthQuadraticInteractionCrossKernelValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Foundations.E6F3DepthQuadraticInteractionCrossKernelReceiptExact as Receipt

depth1ZeroPinned : Receipt.zeroCount Receipt.depth1Zero ≡ 1
depth1ZeroPinned = refl

depth1ZeroQZeroPinned : Receipt.nonzeroQZeroCount Receipt.depth1Zero ≡ 32
depth1ZeroQZeroPinned = refl

depth1NonzeroQOnePinned : Receipt.qOneCount Receipt.depth1Nonzero ≡ 33
depth1NonzeroQOnePinned = refl

depth2BothNonzeroQTwoPinned : Receipt.qTwoCount Receipt.depth2BothNonzero ≡ 9
depth2BothNonzeroQTwoPinned = refl

depth3AllNonzeroQZeroPinned : Receipt.nonzeroQZeroCount Receipt.depth3AllNonzero ≡ 1
depth3AllNonzeroQZeroPinned = refl

nonProductSourceWritten :
  Receipt.nonProductWitnessLeanSourceWritten Receipt.canonicalBoundary ≡ true
nonProductSourceWritten = refl

leanKernelPending : Receipt.leanExactHeadKernelReceiptObserved Receipt.canonicalBoundary ≡ false
leanKernelPending = refl

notIndependentProduct :
  Receipt.depthQuadraticDeclaredIndependentProduct Receipt.canonicalBoundary ≡ false
notIndependentProduct = refl
