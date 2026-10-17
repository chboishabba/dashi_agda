module DASHI.Foundations.E6F3ExteriorSquareRecognitionValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Foundations.E6F3ExteriorSquareRecognitionExact as E6

e6ModelTyped :
  E6.e6Mod3QuadraticModelTyped E6.canonicalE6ExteriorSquareBoundary ≡ true
e6ModelTyped = refl

sameActionTyped :
  E6.PGSp4WE6SameActionRecognitionTyped E6.canonicalE6ExteriorSquareBoundary ≡ true
sameActionTyped = refl

rootLineReceiptTyped :
  E6.rootLineSRG361566ReceiptTyped E6.canonicalE6ExteriorSquareBoundary ≡ true
rootLineReceiptTyped = refl

matrixEqualityNotInvented :
  E6.matrixEqualityKernelProofInThisOwner E6.canonicalE6ExteriorSquareBoundary ≡ false
matrixEqualityNotInvented = refl

rawT4NotPromoted :
  E6.rawT4PuncturePromotedToNullOrbit E6.canonicalE6ExteriorSquareBoundary ≡ false
rawT4NotPromoted = refl
