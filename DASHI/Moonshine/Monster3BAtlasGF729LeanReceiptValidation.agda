module DASHI.Moonshine.Monster3BAtlasGF729LeanReceiptValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Moonshine.Monster3BAtlasGF729LeanReceiptExact as Receipt

leanSameActionSourceWritten :
  Receipt.leanLiteralSameActionSourceWritten Receipt.canonicalBoundary ≡ true
leanSameActionSourceWritten = refl

leanExplicitInverseSourceWritten :
  Receipt.leanExplicitTwoSidedInverseSourceWritten Receipt.canonicalBoundary ≡ true
leanExplicitInverseSourceWritten = refl

leanKernelObservationStillPending :
  Receipt.leanExactHeadKernelReceiptObserved Receipt.canonicalBoundary ≡ false
leanKernelObservationStillPending = refl

agdaKernelReplayStillPending :
  Receipt.agdaLiteralMatrixReplayPaid Receipt.canonicalBoundary ≡ false
agdaKernelReplayStillPending = refl

fullMonsterSemanticsStillOpen :
  Receipt.fullMonsterActionOrbitStabilizerRecognitionPaid Receipt.canonicalBoundary ≡ false
fullMonsterSemanticsStillOpen = refl
