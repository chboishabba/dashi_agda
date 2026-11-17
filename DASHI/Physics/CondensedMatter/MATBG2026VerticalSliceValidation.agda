module DASHI.Physics.CondensedMatter.MATBG2026VerticalSliceValidation where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.CondensedMatter.MATBG2026VerticalSliceExact as MATBG

literalValleyCarrierExists : MATBG.Valley
literalValleyCarrierExists = MATBG.K

timeReverseValleyIsInvolution :
  (v : MATBG.Valley) →
  MATBG.timeReverseValley (MATBG.timeReverseValley v) ≡ v
timeReverseValleyIsInvolution = MATBG.timeReverseValleyInvolutive

qtmMagicAngleHundredths : Nat
qtmMagicAngleHundredths = MATBG.qtmMagicAngleHundredths MATBG.xiao2026QTMObservation

qtmMagicAngleIs110Hundredths :
  qtmMagicAngleHundredths ≡ 110
qtmMagicAngleIs110Hundredths = refl

qtmBestFitW0W1Hundredths : Nat
qtmBestFitW0W1Hundredths =
  MATBG.qtmBestFitW0W1Hundredths MATBG.xiao2026QTMObservation

qtmBestFitW0W1IsSixtyHundredths :
  qtmBestFitW0W1Hundredths ≡ 60
qtmBestFitW0W1IsSixtyHundredths = refl

qtmObservedValleySuperposition : Bool
qtmObservedValleySuperposition =
  MATBG.timeReversalValleySuperposition MATBG.xiao2026QTMObservation

entropyLowDegeneracy : Nat
entropyLowDegeneracy =
  MATBG.lowTemperatureDegeneracy MATBG.zhang2026EntropyObservation

entropyHighDegeneracy : Nat
entropyHighDegeneracy =
  MATBG.highTemperatureDegeneracy MATBG.zhang2026EntropyObservation

entropyLowDegeneracyIsFour : entropyLowDegeneracy ≡ 4
entropyLowDegeneracyIsFour = refl

entropyHighDegeneracyIsEight : entropyHighDegeneracy ≡ 8
entropyHighDegeneracyIsEight = refl

qtmAndEntropySameSampleNotClaimed :
  MATBG.sameSampleQTMEntropyPaid MATBG.canonicalMATBG2026VerticalSlice ≡ false
qtmAndEntropySameSampleNotClaimed = refl

bmDoesNotPayInteractingQTM :
  MATBG.bmSingleParticleExplainsInteractingMagicAngleSpectrum
    MATBG.canonicalMATBG2026VerticalSlice
    ≡ false
bmDoesNotPayInteractingQTM = refl

valleyC3PhysicalIdentificationStillRequiresPayment :
  MATBG.valleyC3SameObjectRepresentationPaid
    MATBG.canonicalMATBG2026VerticalSlice
    ≡ false
valleyC3PhysicalIdentificationStillRequiresPayment = refl
