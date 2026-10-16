module DASHI.Mathematics.Algebra.Ternary27RationalFirstTitsBasicLawWitnessesValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Mathematics.Algebra.Ternary27RationalFirstTitsBasicLawWitnessesExact as Basic

commutativityPaid : Basic.commutativityKernelWitnessPaid Basic.canonicalBasicLawBoundary ≡ true
commutativityPaid = refl

twoSidedUnitPaid : Basic.twoSidedUnitKernelWitnessPaid Basic.canonicalBasicLawBoundary ≡ true
twoSidedUnitPaid = refl

cubicUnitPaid : Basic.cubicUnitKernelWitnessPaid Basic.canonicalBasicLawBoundary ≡ true
cubicUnitPaid = refl

jordanIdentityStillOpen : Basic.jordanIdentityKernelWitnessPaid Basic.canonicalBasicLawBoundary ≡ false
jordanIdentityStillOpen = refl
