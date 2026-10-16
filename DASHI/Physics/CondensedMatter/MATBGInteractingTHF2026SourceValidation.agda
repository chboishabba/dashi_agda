module DASHI.Physics.CondensedMatter.MATBGInteractingTHF2026SourceValidation where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.CondensedMatter.MATBGInteractingTHF2026SourceExact as THF

qtmOnSiteUIs60meV : THF.uMeV THF.xiao2026THFParameters ≡ 60
qtmOnSiteUIs60meV = refl

qtmHybridizationMagnitudeIs70meV : THF.magnitude (THF.gammaMeV THF.xiao2026THFParameters) ≡ 70
qtmHybridizationMagnitudeIs70meV = refl

qtmLifetimeBroadeningIs1meV : THF.inverseLifetimeMeV THF.xiao2026THFParameters ≡ 1
qtmLifetimeBroadeningIs1meV = refl

qtmEightStateFCarrier : THF.fStateCount THF.xiao2026THFParameters ≡ 8
qtmEightStateFCarrier = refl

entropyLowPlateauDegeneracyIsFour : THF.lowTemperatureDegeneracy THF.zhang2026EntropyTHFReceipt ≡ 4
entropyLowPlateauDegeneracyIsFour = refl

entropyHighPlateauDegeneracyIsEight : THF.highTemperatureDegeneracy THF.zhang2026EntropyTHFReceipt ≡ 8
entropyHighPlateauDegeneracyIsEight = refl

qtmAndEntropyDoNotBecomeSameSample : THF.sameSampleQTMEntropyPaid THF.canonicalTHF2026Boundary ≡ false
qtmAndEntropyDoNotBecomeSameSample = refl

sourceParametersDoNotCreateSelfConsistentSolve : THF.selfConsistentInteractingSolvePaid THF.canonicalTHF2026Boundary ≡ false
sourceParametersDoNotCreateSelfConsistentSolve = refl
