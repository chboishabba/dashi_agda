module DASHI.Foundations.E6F3RootLineSRGCrossKernelValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Foundations.E6F3RootLineSRGCrossKernelReceiptExact as Receipt

vertexCountPinned : Receipt.vertexCount Receipt.canonicalReceipt ≡ 36
vertexCountPinned = refl

degreePinned : Receipt.degree Receipt.canonicalReceipt ≡ 15
degreePinned = refl

adjacentCommonPinned : Receipt.adjacentCommon Receipt.canonicalReceipt ≡ 6
adjacentCommonPinned = refl

nonAdjacentCommonPinned : Receipt.nonAdjacentCommon Receipt.canonicalReceipt ≡ 6
nonAdjacentCommonPinned = refl

srgSourceWritten : Receipt.srg361566LeanSourceWritten Receipt.canonicalBoundary ≡ true
srgSourceWritten = refl

leanKernelStillPending : Receipt.leanExactHeadKernelReceiptObserved Receipt.canonicalBoundary ≡ false
leanKernelStillPending = refl

noPhysicalPromotion : Receipt.srgCreatesPhysicalOrSemanticMechanism Receipt.canonicalBoundary ≡ false
noPhysicalPromotion = refl
