module DASHI.Moonshine.OggSSPMonster3BSelectedGF729WeldValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Moonshine.OggSSPMonster3BSelectedGF729WeldExact as Weld

matrixBytesNowAcquired :
  Weld.actualAtlasMatrixBytesAcquired Weld.canonicalBoundary ≡ true
matrixBytesNowAcquired = refl

degreeSixCompressionNowPaid :
  Weld.degreeSixCompressionReceiptPaid Weld.canonicalBoundary ≡ true
degreeSixCompressionNowPaid = refl

selectedFieldPresentationNowWelded :
  Weld.selectedGF729PresentationWeldPaid Weld.canonicalBoundary ≡ true
selectedFieldPresentationNowWelded = refl

agdaMatrixKernelProofStillOpen :
  Weld.agdaKernelIntertwinerProofPaid Weld.canonicalBoundary ≡ false
agdaMatrixKernelProofStillOpen = refl

fullActionRecognitionStillOpen :
  Weld.fullActionOrbitStabilizerRecognitionPaid Weld.canonicalBoundary ≡ false
fullActionRecognitionStillOpen = refl

intertwinerDeterminantIsTwo : Weld.intertwinerDeterminantMod3 ≡ 2
intertwinerDeterminantIsTwo = refl
