{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.GRQFTCMP119NambuBuriedVacuumReadoutExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ)

import DASHI.Physics.YangMills.BalabanCMP119Section2SourceNativeStateExact as Source
import DASHI.Physics.YangMills.BalabanClayT4LocalizedPlaquetteCoefficientProducerExact as T4
import DASHI.Physics.Foundations.GRQFTCMP119SourceNativeVacuumAmplitudeBidiExact as Vacuum

------------------------------------------------------------------------
-- BURIED READOUT RECOVERY
--
-- The source-native Nambu lane previously described a rational readout
--   Vacuum -> Q
-- as absent.  That is too pessimistic in the existing LocalizedAction
-- realization already used by the CMP119 antigravity/action projector lane:
-- `plaquetteCoefficientProjector` is exactly such a map and is already applied
-- to the literal source-native `vacuumEnergy` term elsewhere in-repo.
--
-- This closes the readout-CARRIER leaf only.  It deliberately does not assert
-- that any two source scales have the geometry-selected values 21/64, 19/48.
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
    sourceVacuumAmplitudeAt interiorScale
      ≡ Data.Integer.Base.+ 21 Data.Rational.Base./ 64 →
    sourceVacuumAmplitudeAt exteriorScale
      ≡ Data.Integer.Base.+ 19 Data.Rational.Base./ 48 →
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
