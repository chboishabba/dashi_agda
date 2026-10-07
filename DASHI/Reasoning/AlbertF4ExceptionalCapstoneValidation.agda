module DASHI.Reasoning.AlbertF4ExceptionalCapstoneValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Reasoning.AlbertF4ExceptionalCapstoneExact as Albert

externalDonorPinned :
  Albert.externalAlbertDonorPinned Albert.currentAlbertF4Frontier ≡ true
externalDonorPinned = refl

scalarTracelessSourceWritten :
  Albert.leanScalarTracelessLinearEquivalenceSourceWritten Albert.currentAlbertF4Frontier ≡ true
scalarTracelessSourceWritten = refl

minusculeWeightLineTyped :
  Albert.minusculeWeightLineReceiptTypedInAgda Albert.currentAlbertF4Frontier ≡ true
minusculeWeightLineTyped = refl

f4StillOpen :
  Albert.actualF4AutomorphismRecognitionPaid Albert.currentAlbertF4Frontier ≡ false
f4StillOpen = refl

ternaryBasisStillOpen :
  Albert.actualTernaryOnePlus26BasisWeldPaid Albert.currentAlbertF4Frontier ≡ false
ternaryBasisStillOpen = refl

fullE8StillOpen :
  Albert.fullTernary240E8RecognitionPaid Albert.currentAlbertF4Frontier ≡ false
fullE8StillOpen = refl
