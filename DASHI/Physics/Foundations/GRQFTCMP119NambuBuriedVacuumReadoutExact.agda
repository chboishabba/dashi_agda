{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.GRQFTCMP119NambuBuriedVacuumReadoutExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; _/_)

import DASHI.Physics.YangMills.BalabanCMP119Section2SourceNativeStateExact as Source
import DASHI.Physics.YangMills.BalabanClayT4LocalizedPlaquetteCoefficientProducerExact as T4
import DASHI.Physics.Foundations.GRQFTCMP119SourceNativeVacuumAmplitudeBidiExact as Vacuum

------------------------------------------------------------------------
-- BURIED READOUT RECOVERY
--
-- In the LocalizedAction realization already used by the CMP119 antigravity
-- action projector lane, `plaquetteCoefficientProjector` is the rational
-- readout of the literal source-native `vacuumEnergy` term.  This closes only
-- the readout-carrier leaf; the two selected source values remain theorems to
-- prove on the actual source scales.
------------------------------------------------------------------------

localizedVacuumReadout :
  Vacuum.VacuumEnergyRationalReadout T4.LocalizedAction
localizedVacuumReadout = record
  { Vacuum.VacuumEnergyRationalReadout.vacuumToRat =
      T4.plaquetteCoefficientProjector }

module _
  {Density Background Fluctuation : Set}
  (source : Source.CMP119Section2SourceNativeState
    Density Background Fluctuation
    T4.LocalizedAction T4.LocalizedAction T4.LocalizedAction
    T4.LocalizedAction T4.LocalizedAction T4.LocalizedAction)
  where

  sourceVacuumAmplitudeAt : Nat → ℚ
  sourceVacuumAmplitudeAt scale =
    T4.plaquetteCoefficientProjector
      (Source.vacuumEnergy source scale)

  sourceVacuumAmplitudeUsesBuriedReadout : ∀ scale →
    sourceVacuumAmplitudeAt scale
    ≡ Vacuum.vacuumToRat localizedVacuumReadout
        (Source.vacuumEnergy source scale)
  sourceVacuumAmplitudeUsesBuriedReadout scale = refl

  nambuAmplitudeReceiptFromExistingReadout :
    (interiorScale exteriorScale : Nat) →
    sourceVacuumAmplitudeAt interiorScale ≡ Int.+ 21 / 64 →
    sourceVacuumAmplitudeAt exteriorScale ≡ Int.+ 19 / 48 →
    Vacuum.SourceNativeNambuVacuumAmplitudeReceipt source
  nambuAmplitudeReceiptFromExistingReadout
      interiorScale exteriorScale interiorValue exteriorValue = record
    { Vacuum.SourceNativeNambuVacuumAmplitudeReceipt.readout =
        localizedVacuumReadout
    ; Vacuum.SourceNativeNambuVacuumAmplitudeReceipt.interiorScale =
        interiorScale
    ; Vacuum.SourceNativeNambuVacuumAmplitudeReceipt.exteriorScale =
        exteriorScale
    ; Vacuum.SourceNativeNambuVacuumAmplitudeReceipt.interiorAmplitude =
        interiorValue
    ; Vacuum.SourceNativeNambuVacuumAmplitudeReceipt.exteriorAmplitude =
        exteriorValue
    }

record BuriedVacuumReadoutBoundary : Set where
  constructor buried-vacuum-readout-boundary
  field
    readoutCarrierAlreadyExists : Bool
    readoutUsesLiteralSourceVacuumEnergy : Bool
    readoutUsesExistingPlaquetteProjector : Bool
    independentVacuumToRationalMapStillNeeded : Bool
    twoSelectedSourceValuesStillNeedProof : Bool

canonicalBuriedVacuumReadoutBoundary : BuriedVacuumReadoutBoundary
canonicalBuriedVacuumReadoutBoundary =
  buried-vacuum-readout-boundary true true true false true
