module DASHI.Moonshine.Monster3BAtlasSelectedHeisenbergLiftReceiptValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Moonshine.Monster3BAtlasSelectedHeisenbergLiftReceiptExact as Lift

selectedWordMatrixPaid :
  Lift.selectedWordMatrixRuntimePaid Lift.canonicalBoundary ≡ true
selectedWordMatrixPaid = refl

strictSymplecticMultiplierPaid :
  Lift.selectedWordStrictSymplecticPaid Lift.canonicalBoundary ≡ true
strictSymplecticMultiplierPaid = refl

quadraticCorrectionPaid :
  Lift.selectedWordQuadraticCentralCorrectionPaid Lift.canonicalBoundary ≡ true
quadraticCorrectionPaid = refl

fullNormalizerLiftStillOpen :
  Lift.fullNormalizerHeisenbergActionPaid Lift.canonicalBoundary ≡ false
fullNormalizerLiftStillOpen = refl
