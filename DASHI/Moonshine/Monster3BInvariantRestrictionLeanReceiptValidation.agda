module DASHI.Moonshine.Monster3BInvariantRestrictionLeanReceiptValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Moonshine.Monster3BInvariantRestrictionLeanReceiptExact as Receipt

restrictionCompilerPresent :
  Receipt.restrictedRepresentationCompilerSourceWritten Receipt.canonicalBoundary ≡ true
restrictionCompilerPresent = refl

linearityIsCompilerOutput :
  Receipt.restrictionLinearityCompilerOutput Receipt.canonicalBoundary ≡ true
linearityIsCompilerOutput = refl

actualInvariantSubspacesRemainOpen :
  Receipt.actualMonsterInvariantSubspacePaidByReceipt Receipt.canonicalBoundary ≡ false
actualInvariantSubspacesRemainOpen = refl
