module DASHI.Mathematics.Algebra.Ternary27RationalFirstTitsUnitWitnessValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Mathematics.Algebra.Ternary27RationalFirstTitsUnitWitnessExact as Unit

leftUnitTermSourceWritten : Unit.leftUnitProofTermSourceWritten Unit.canonicalUnitBoundary ≡ true
leftUnitTermSourceWritten = refl

rightUnitTermSourceWritten : Unit.rightUnitProofTermSourceWritten Unit.canonicalUnitBoundary ≡ true
rightUnitTermSourceWritten = refl

kernelStillPending : Unit.exactHeadAgdaKernelReceiptPresent Unit.canonicalUnitBoundary ≡ false
kernelStillPending = refl
