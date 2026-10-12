module DASHI.Moonshine.OggSSPMonster3BSelectedGF729WeldValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Moonshine.OggSSPMonster3BSelectedGF729WeldExact as Weld

matrixBytesNowAcquired :
  Weld.actualAtlasMatrixBytesAcquired Weld.canonicalBoundary ≡ true
matrixBytesNowAcquired = refl

degreeSixCompressionNowPaid :
  Weld.degreeSixCompressionReceiptPaid Weld.canonicalBoundary ≡ true
degreeSixCompressionNowPaid = refl

primitiveRootNowPaid :
  Weld.selectedGF729PrimitiveOrder728Paid Weld.canonicalBoundary ≡ true
primitiveRootNowPaid = refl

selectedFieldPresentationNowWelded :
  Weld.selectedGF729PresentationWeldPaid Weld.canonicalBoundary ≡ true
selectedFieldPresentationNowWelded = refl

selectedFieldMultiplicativeActionNowWelded :
  Weld.selectedGF729MultiplicativeActionWeldPaid Weld.canonicalBoundary ≡ true
selectedFieldMultiplicativeActionNowWelded = refl

puncturedOrbit728NowPaid :
  Weld.selectedGF729PuncturedOrbit728Paid Weld.canonicalBoundary ≡ true
puncturedOrbit728NowPaid = refl

puncturedStabilizerNowTrivial :
  Weld.selectedGF729PuncturedStabilizerTrivialPaid Weld.canonicalBoundary ≡ true
puncturedStabilizerNowTrivial = refl

primitiveOrderIs728 : Weld.selectedGammaMultiplicativeOrder ≡ 728
primitiveOrderIs728 = refl

puncturedOrbitSizeIs728 : Weld.puncturedOrbitSize ≡ 728
puncturedOrbitSizeIs728 = refl

puncturedStabilizerSizeIsOne : Weld.puncturedStabilizerSize ≡ 1
puncturedStabilizerSizeIsOne = refl

agdaMatrixKernelProofStillOpen :
  Weld.agdaKernelIntertwinerProofPaid Weld.canonicalBoundary ≡ false
agdaMatrixKernelProofStillOpen = refl

fullMonsterSemanticActionRecognitionStillOpen :
  Weld.fullActionOrbitStabilizerRecognitionPaid Weld.canonicalBoundary ≡ false
fullMonsterSemanticActionRecognitionStillOpen = refl

intertwinerDeterminantIsTwo : Weld.intertwinerDeterminantMod3 ≡ 2
intertwinerDeterminantIsTwo = refl
