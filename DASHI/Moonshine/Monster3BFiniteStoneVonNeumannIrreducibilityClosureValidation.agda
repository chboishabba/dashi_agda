module DASHI.Moonshine.Monster3BFiniteStoneVonNeumannIrreducibilityClosureValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Moonshine.Monster3BFiniteStoneVonNeumannIrreducibilityClosureExact as Closure

ordinaryNonzeroCoordinateExtractionClosed :
  Closure.arbitraryNonzeroVectorYieldsSelectedNonzeroCoordinate
    Closure.canonicalBoundary ≡ true
ordinaryNonzeroCoordinateExtractionClosed = refl

schrodingerIrreducibilityClosed :
  Closure.schrodingerIrreducibilityPaid Closure.canonicalBoundary ≡ true
schrodingerIrreducibilityClosed = refl

fixedCentralCharacterUniquenessStillOpen :
  Closure.fixedCentralCharacterUniquenessPaid Closure.canonicalBoundary ≡ false
fixedCentralCharacterUniquenessStillOpen = refl

actualMonster729SameObjectStillOpen :
  Closure.actualMonster729IdentificationPaid Closure.canonicalBoundary ≡ false
actualMonster729SameObjectStillOpen = refl
