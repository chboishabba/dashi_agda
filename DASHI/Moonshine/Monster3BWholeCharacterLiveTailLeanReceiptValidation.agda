module DASHI.Moonshine.Monster3BWholeCharacterLiveTailLeanReceiptValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Moonshine.Monster3BWholeCharacterLiveTailLeanReceiptExact as R

adapterPaid : R.fdrepModuleAdapterSourceWritten R.canonicalBoundary ≡ true
adapterPaid = refl

classifierPaid : R.wholeCharacterSimpleSourceClassifierSourceWritten R.canonicalBoundary ≡ true
classifierPaid = refl

maschkePaid : R.maschkeSemisimplicitySourceWritten R.canonicalBoundary ≡ true
maschkePaid = refl

actualCharacterTransportOpen : R.actualMonsterWholeCharacterTransportPaidByReceipt R.canonicalBoundary ≡ false
actualCharacterTransportOpen = refl
