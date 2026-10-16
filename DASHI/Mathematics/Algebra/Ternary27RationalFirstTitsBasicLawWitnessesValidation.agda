module DASHI.Mathematics.Algebra.Ternary27RationalFirstTitsBasicLawWitnessesValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Mathematics.Algebra.Ternary27RationalFirstTitsBasicLawWitnessesExact as Basic

commutativityPaid : Basic.commutativityKernelWitnessSourceWritten Basic.canonicalBasicLawBoundary ≡ true
commutativityPaid = refl

cubicUnitPaid : Basic.cubicUnitKernelWitnessSourceWritten Basic.canonicalBasicLawBoundary ≡ true
cubicUnitPaid = refl

twoSidedUnitStillOpen : Basic.twoSidedUnitKernelWitnessPaid Basic.canonicalBasicLawBoundary ≡ false
twoSidedUnitStillOpen = refl

jordanIdentityStillOpen : Basic.jordanIdentityKernelWitnessPaid Basic.canonicalBasicLawBoundary ≡ false
jordanIdentityStillOpen = refl
