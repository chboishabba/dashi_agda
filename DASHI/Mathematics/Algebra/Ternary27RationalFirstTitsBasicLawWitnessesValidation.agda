module DASHI.Mathematics.Algebra.Ternary27RationalFirstTitsBasicLawWitnessesValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Mathematics.Algebra.Ternary27RationalFirstTitsBasicLawWitnessesExact as Basic

commutativitySourceWritten :
  Basic.commutativityProofTermSourceWritten Basic.canonicalBasicLawBoundary ≡ true
commutativitySourceWritten = refl

cubicUnitSourceWritten :
  Basic.cubicUnitProofTermSourceWritten Basic.canonicalBasicLawBoundary ≡ true
cubicUnitSourceWritten = refl

fullPackageStillOpen :
  Basic.fullPaidLawPackageInhabited Basic.canonicalBasicLawBoundary ≡ false
fullPackageStillOpen = refl

kernelReceiptStillPending :
  Basic.exactHeadAgdaKernelReceiptPresent Basic.canonicalBasicLawBoundary ≡ false
kernelReceiptStillPending = refl
