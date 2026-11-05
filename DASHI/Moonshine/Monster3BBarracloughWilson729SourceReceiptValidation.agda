module DASHI.Moonshine.Monster3BBarracloughWilson729SourceReceiptValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Moonshine.Monster3BBarracloughWilson729SourceReceiptExact as Receipt

degree729SourcePaid :
  Receipt.sourceStatesTwoDegree729ExtraspecialCharacters Receipt.canonicalBoundary ≡ true
degree729SourcePaid = refl

extensionToSixSuzPaid :
  Receipt.sourceStatesBothExtendToSixSuzInertia Receipt.canonicalBoundary ≡ true
extensionToSixSuzPaid = refl

ninetyCharactersNotMultiplicity :
  Receipt.section6NinetyCharactersIdentifiedWithModelFin90 Receipt.canonicalBoundary ≡ false
ninetyCharactersNotMultiplicity = refl

actualZetaBasisStillOpen :
  Receipt.actualWzetaToX6Fin90SameObjectPaid Receipt.canonicalBoundary ≡ false
actualZetaBasisStillOpen = refl
