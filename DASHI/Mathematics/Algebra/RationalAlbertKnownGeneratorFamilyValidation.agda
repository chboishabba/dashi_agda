module DASHI.Mathematics.Algebra.RationalAlbertKnownGeneratorFamilyValidation where

open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Mathematics.Algebra.RationalAlbertKnownGeneratorFamilyExact as G

allFiveKnownGeneratorsProductPreserving :
  G.allKnownGeneratorsProductPreserving G.canonicalKnownGeneratorBoundary ≡ true
allFiveKnownGeneratorsProductPreserving = refl

allFiveKnownGeneratorsCubicPreserving :
  G.allKnownGeneratorsCubicPreserving G.canonicalKnownGeneratorBoundary ≡ true
allFiveKnownGeneratorsCubicPreserving = refl
