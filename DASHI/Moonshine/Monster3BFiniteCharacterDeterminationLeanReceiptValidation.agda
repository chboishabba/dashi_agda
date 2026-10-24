module DASHI.Moonshine.Monster3BFiniteCharacterDeterminationLeanReceiptValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Moonshine.Monster3BFiniteCharacterDeterminationLeanReceiptExact as Receipt

leanGenericTheoremSourceWritten :
  Receipt.leanEqualCharacterSimpleIsoSourceWritten Receipt.canonicalBoundary ≡ true
leanGenericTheoremSourceWritten = refl

algebraicClosureNotRequired :
  Receipt.algebraicClosureRequiredByLeanTheorem Receipt.canonicalBoundary ≡ false
algebraicClosureNotRequired = refl

leanKernelObservationPending :
  Receipt.leanExactHeadKernelReceiptObserved Receipt.canonicalBoundary ≡ false
leanKernelObservationPending = refl

monsterCarrierTransportStillOpen :
  Receipt.monsterFiniteHeisenbergFDRepTransportPaid Receipt.canonicalBoundary ≡ false
monsterCarrierTransportStillOpen = refl
