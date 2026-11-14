module DASHI.Moonshine.Monster3BLinearEigenspaceRestrictionLeanReceiptValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Moonshine.Monster3BLinearEigenspaceRestrictionLeanReceiptExact as Receipt

literalEigenspaceCompilerPresent :
  Receipt.literalLinearEigenspaceCompilerSourceWritten Receipt.canonicalBoundary ≡ true
literalEigenspaceCompilerPresent = refl

invarianceCompilerPresent :
  Receipt.commutingActionPreservesEigenspaceSourceWritten Receipt.canonicalBoundary ≡ true
invarianceCompilerPresent = refl

actualCentralOperatorOpen :
  Receipt.actualMonsterCentralLinearOperatorPaidByReceipt Receipt.canonicalBoundary ≡ false
actualCentralOperatorOpen = refl
