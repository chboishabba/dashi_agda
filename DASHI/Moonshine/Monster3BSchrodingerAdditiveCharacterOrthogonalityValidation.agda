module DASHI.Moonshine.Monster3BSchrodingerAdditiveCharacterOrthogonalityValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Algebra.Trit using (neg; zer; pos)

import DASHI.Moonshine.C3CyclotomicAmplitudeAlgebraExact as C3
import DASHI.Moonshine.Monster3BFiniteHeisenbergGeneratorsExact as H
import DASHI.Moonshine.Monster3BSchrodingerAdditiveCharacterOrthogonalityExact as Orth

negCoordinateCancels : Orth.phaseWeightedSum neg ≡ C3.zero
negCoordinateCancels = Orth.phaseWeightedSumNeg

posCoordinateCancels : Orth.phaseWeightedSum pos ≡ C3.zero
posCoordinateCancels = Orth.phaseWeightedSumPos

zeroVectorSumIs729 :
  Orth.factorizedModulationCharacter (H.x6 zer zer zer zer zer zer)
  ≡ Orth.sevenHundredTwentyNine
zeroVectorSumIs729 = Orth.factorizedZeroVector

nonzeroFirstCoordinateCancels :
  Orth.factorizedModulationCharacter (H.x6 pos zer zer zer zer zer)
  ≡ C3.zero
nonzeroFirstCoordinateCancels =
  Orth.factorizedNonzeroVector
    (H.x6 pos zer zer zer zer zer)
    (Orth.coordinate0 Orth.posNonzero)

kernelOrthogonalityCorePaid :
  Orth.factorizedAdditiveCharacterOrthogonalityPaid Orth.canonicalBoundary ≡ true
kernelOrthogonalityCorePaid = refl

literalNestedTraceBridgeStillSeparate :
  Orth.literalNestedBasisSumIdentifiedHere Orth.canonicalBoundary ≡ false
literalNestedTraceBridgeStillSeparate = refl
