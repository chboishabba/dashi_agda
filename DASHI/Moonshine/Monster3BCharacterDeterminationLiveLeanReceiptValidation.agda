module DASHI.Moonshine.Monster3BCharacterDeterminationLiveLeanReceiptValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Moonshine.Monster3BCharacterDeterminationLiveLeanReceiptExact as R

twoSimpleMultiplicityPaid : R.twoSimpleCharacterMultiplicitySourceWritten R.canonicalBoundary ≡ true
twoSimpleMultiplicityPaid = refl

intertwinerNotIndependent : R.twelveSeventyEightIntertwinerStillIndependentInput R.canonicalBoundary ≡ false
intertwinerNotIndependent = refl

actualTransportOpen : R.actualSuzukiMultiplicityCharacterTransportPaidByReceipt R.canonicalBoundary ≡ false
actualTransportOpen = refl
