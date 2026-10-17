module DASHI.Moonshine.Monster3BNormalizerHomActionLeanReceiptValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Moonshine.Monster3BNormalizerHomActionLeanReceiptExact as R

homActionCompilerPaid : R.inducedHomNormalizerActionSourceWritten R.canonicalBoundary ≡ true
homActionCompilerPaid = refl

multiplicityActionNotIndependent : R.independentMultiplicityActionStillRequired R.canonicalBoundary ≡ false
multiplicityActionNotIndependent = refl

actualLiftsOpen : R.actualMonsterNormalizerLiftsPaidByReceipt R.canonicalBoundary ≡ false
actualLiftsOpen = refl
