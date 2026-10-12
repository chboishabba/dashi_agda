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

leanPrimitiveOrderSourceWritten :
  Receipt.leanPrimitiveOrder728SourceWritten Receipt.canonicalBoundary ≡ true
leanPrimitiveOrderSourceWritten = refl

leanPrimitiveOrbitSourceWritten :
  Receipt.leanPuncturedOrbit728SourceWritten Receipt.canonicalBoundary ≡ true
leanPrimitiveOrbitSourceWritten = refl

leanPrimitiveStabilizerSourceWritten :
  Receipt.leanPuncturedStabilizerTrivialSourceWritten Receipt.canonicalBoundary ≡ true
leanPrimitiveStabilizerSourceWritten = refl

leanKernelObservationStillPending :
  Receipt.leanExactHeadKernelReceiptObserved Receipt.canonicalBoundary ≡ false
leanKernelObservationStillPending = refl

agdaKernelReplayStillPending :
  Receipt.agdaLiteralMatrixReplayPaid Receipt.canonicalBoundary ≡ false
agdaKernelReplayStillPending = refl

fullMonsterSemanticsStillOpen :
  Receipt.fullMonsterSemanticActionRecognitionPaid Receipt.canonicalBoundary ≡ false
fullMonsterSemanticsStillOpen = refl
