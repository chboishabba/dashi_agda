module DASHI.Moonshine.Monster3BTensorFiniteCopiesLeanReceiptValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Moonshine.Monster3BTensorFiniteCopiesLeanReceiptExact as R

tensorCompilerPaid : R.tensorFiniteCopiesCompilerSourceWritten R.canonicalBoundary ≡ true
tensorCompilerPaid = refl

postIsotypyPaid : R.postIsotypyTensorEquivalenceSourceWritten R.canonicalBoundary ≡ true
postIsotypyPaid = refl

tensorNotIndependentMonsterInput : R.tensorEquivalenceStillMonsterSpecificInput R.canonicalBoundary ≡ false
tensorNotIndependentMonsterInput = refl
