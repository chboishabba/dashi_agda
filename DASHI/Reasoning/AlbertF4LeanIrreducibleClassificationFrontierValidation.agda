module DASHI.Reasoning.AlbertF4LeanIrreducibleClassificationFrontierValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Reasoning.AlbertF4LeanIrreducibleClassificationFrontierReceiptExact as Receipt

singleWitnessPinned :
  Receipt.terminalResidualReducedToSingleDependentWitness Receipt.canonicalBoundary ≡ true
singleWitnessPinned = refl

finalInputStillOpen :
  Receipt.finalClassificationInputInhabitedInLean Receipt.canonicalBoundary ≡ false
finalInputStillOpen = refl

noAgdaAuthorityImport :
  Receipt.leanProofAuthorityImportedIntoAgda Receipt.canonicalBoundary ≡ false
noAgdaAuthorityImport = refl
