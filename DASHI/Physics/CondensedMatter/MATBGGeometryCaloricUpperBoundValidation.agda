module DASHI.Physics.CondensedMatter.MATBGGeometryCaloricUpperBoundValidation where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.CondensedMatter.MATBGGeometryCaloricUpperBoundReceiptExact as Caloric

entropySwingExecutionPaid : Caloric.entropySwingExecutionPaid Caloric.canonicalGeometryCaloricUpperBoundBoundary ≡ true
entropySwingExecutionPaid = refl

controlledCycleStillFalse : Caloric.controlledGeometryCyclePaid Caloric.canonicalGeometryCaloricUpperBoundBoundary ≡ false
controlledCycleStillFalse = refl

usefulCoolingStillFalse : Caloric.usefulCoolingPaid Caloric.canonicalGeometryCaloricUpperBoundBoundary ≡ false
usefulCoolingStillFalse = refl
