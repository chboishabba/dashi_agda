module DASHI.Analysis.CollatzSyracuseCoefficientResonanceValidation where

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Analysis.CollatzSyracuseCoefficientResonanceExact as Resonance

coefficientCoordinatePaid :
  Resonance.CoefficientResonanceBoundary.exactCoefficientCoordinatePaid
    Resonance.canonicalCoefficientResonanceBoundary
  ≡ 1
coefficientCoordinatePaid = refl

oddCountCollisionPaid :
  Resonance.CoefficientResonanceBoundary.sameCountSameCoefficientDifferentCorrectionWitnessPaid
    Resonance.canonicalCoefficientResonanceBoundary
  ≡ 1
oddCountCollisionPaid = refl

continuedFractionNotImported :
  Resonance.CoefficientResonanceBoundary.continuedFractionObservationImportedAsUniversalTheorem
    Resonance.canonicalCoefficientResonanceBoundary
  ≡ 0
continuedFractionNotImported = refl
