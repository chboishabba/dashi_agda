{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityLocalizedVacuumReadoutExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; _/_)

import DASHI.Physics.YangMills.BalabanCMP119Section2SourceNativeStateExact as Source
import DASHI.Physics.YangMills.BalabanClayT4LocalizedPlaquetteCoefficientProducerExact as T4
import DASHI.Physics.Foundations.GRQFTCMP119SourceNativeVacuumAmplitudeBidiExact as Vacuum

------------------------------------------------------------------------
-- SOURCE-NATIVE VACUUM READOUT REUSE
--
-- On the concrete LocalizedAction realization already used by the CMP119
-- antigravity beta/action lane, the vacuum carrier is not opaque: it is the
-- same LocalizedAction carrier as the other Eq.(2.23) sectors.  The existing
-- plaquetteCoefficientProjector therefore supplies a canonical rational
-- readout.  No second arbitrary Vacuum -> Q map is required.
--
-- This does NOT manufacture the two target amplitudes.  Those remain literal
-- source-value equalities at two selected scales.
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

  localizedVacuumValue : Nat → ℚ
  localizedVacuumValue scale =
    T4.plaquetteCoefficientProjector
      (Source.vacuumEnergy source scale)

  sourceNativeAmplitudeReceiptFromProjectedVacua :
    (interiorScale exteriorScale : Nat) →
    localizedVacuumValue interiorScale ≡ Int.+ 21 / 64 →
    localizedVacuumValue exteriorScale ≡ Int.+ 19 / 48 →
    Vacuum.SourceNativeNambuVacuumAmplitudeReceipt source
  sourceNativeAmplitudeReceiptFromProjectedVacua
      interiorScale exteriorScale interior exterior = record
    { Vacuum.SourceNativeNambuVacuumAmplitudeReceipt.readout =
        localizedVacuumReadout
    ; Vacuum.SourceNativeNambuVacuumAmplitudeReceipt.interiorScale =
        interiorScale
    ; Vacuum.SourceNativeNambuVacuumAmplitudeReceipt.exteriorScale =
        exteriorScale
    ; Vacuum.SourceNativeNambuVacuumAmplitudeReceipt.interiorAmplitude =
        interior
    ; Vacuum.SourceNativeNambuVacuumAmplitudeReceipt.exteriorAmplitude =
        exterior
    }

record LocalizedVacuumReadoutBoundary : Set where
  constructor localized-vacuum-readout-boundary
  field
    localizedVacuumCarrierAlreadyRationallyProjectable : Bool
    projectorReusedFromExistingActionLane : Bool
    independentVacuumReadoutStillRequired : Bool
    twoSourceAmplitudeEqualitiesStillRequired : Bool

canonicalLocalizedVacuumReadoutBoundary : LocalizedVacuumReadoutBoundary
canonicalLocalizedVacuumReadoutBoundary =
  localized-vacuum-readout-boundary true true false true
