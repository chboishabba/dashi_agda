{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityLocalizedVacuumReadoutExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; 0ℚ; _/_)
open import Relation.Binary.PropositionalEquality using (trans)

import DASHI.Physics.YangMills.BalabanCMP119Section2SourceNativeStateExact as Source
import DASHI.Physics.YangMills.BalabanClayT4LocalizedPlaquetteCoefficientProducerExact as T4
import DASHI.Physics.Foundations.GRQFTCMP119SourceNativeVacuumAmplitudeBidiExact as Vacuum

------------------------------------------------------------------------
-- SOURCE-NATIVE VACUUM CONSTANT READOUT
--
-- LocalizedAction has TWO rational coordinates.  The plaquette coefficient is
-- the Wilson/plaquette-relevant coordinate; an additive vacuum/normalization
-- constant is naturally carried by the non-plaquette remainder coordinate.
--
-- Therefore the preferred readout is irrelevantCoefficientField, not
-- plaquetteCoefficientProjector.  A further published-source semantic receipt
-- is still required before the selected CMP119 vacuumEnergy term is identified
-- with a pure constant action `irrelevantAction V`.
------------------------------------------------------------------------

localizedVacuumConstantReadout :
  Vacuum.VacuumEnergyRationalReadout T4.LocalizedAction
localizedVacuumConstantReadout = record
  { Vacuum.VacuumEnergyRationalReadout.vacuumToRat =
      T4.irrelevantCoefficientField }

-- Compatibility name retained for existing consumers; it now denotes the
-- constant/remainder coordinate.
localizedVacuumReadout :
  Vacuum.VacuumEnergyRationalReadout T4.LocalizedAction
localizedVacuumReadout = localizedVacuumConstantReadout

module _
  {Density Background Fluctuation : Set}
  (source : Source.CMP119Section2SourceNativeState
    Density Background Fluctuation
    T4.LocalizedAction T4.LocalizedAction T4.LocalizedAction
    T4.LocalizedAction T4.LocalizedAction T4.LocalizedAction)
  where

  localizedVacuumValue : Nat → ℚ
  localizedVacuumValue scale =
    T4.irrelevantCoefficientField
      (Source.vacuumEnergy source scale)

  record VacuumConstantEncodingReceipt : Set where
    field
      vacuumConstantAt : Nat → ℚ
      vacuumSectorIsConstantAction :
        ∀ scale →
        Source.vacuumEnergy source scale
        ≡ T4.irrelevantAction (vacuumConstantAt scale)

  open VacuumConstantEncodingReceipt public

  vacuumConstantReadoutMatchesEncoding :
    (receipt : VacuumConstantEncodingReceipt) →
    ∀ scale →
    localizedVacuumValue scale ≡ vacuumConstantAt receipt scale
  vacuumConstantReadoutMatchesEncoding receipt scale
    rewrite vacuumSectorIsConstantAction receipt scale = refl

  vacuumConstantEncodingHasZeroPlaquetteProjection :
    (receipt : VacuumConstantEncodingReceipt) →
    ∀ scale →
    T4.plaquetteCoefficientProjector
      (Source.vacuumEnergy source scale) ≡ 0ℚ
  vacuumConstantEncodingHasZeroPlaquetteProjection receipt scale
    rewrite vacuumSectorIsConstantAction receipt scale = refl

  sourceNativeAmplitudeReceiptFromConstantVacua :
    (encoding : VacuumConstantEncodingReceipt) →
    (interiorScale exteriorScale : Nat) →
    vacuumConstantAt encoding interiorScale ≡ Int.+ 21 / 64 →
    vacuumConstantAt encoding exteriorScale ≡ Int.+ 19 / 48 →
    Vacuum.SourceNativeNambuVacuumAmplitudeReceipt source
  sourceNativeAmplitudeReceiptFromConstantVacua
      encoding interiorScale exteriorScale interior exterior = record
    { Vacuum.SourceNativeNambuVacuumAmplitudeReceipt.readout =
        localizedVacuumConstantReadout
    ; Vacuum.SourceNativeNambuVacuumAmplitudeReceipt.interiorScale =
        interiorScale
    ; Vacuum.SourceNativeNambuVacuumAmplitudeReceipt.exteriorScale =
        exteriorScale
    ; Vacuum.SourceNativeNambuVacuumAmplitudeReceipt.interiorAmplitude =
        trans (vacuumConstantReadoutMatchesEncoding encoding interiorScale) interior
    ; Vacuum.SourceNativeNambuVacuumAmplitudeReceipt.exteriorAmplitude =
        trans (vacuumConstantReadoutMatchesEncoding encoding exteriorScale) exterior
    }

  -- Historical compatibility constructor.  It is now deliberately typed over
  -- the corrected constant-coordinate readout rather than the plaquette
  -- projector.  It does not by itself prove the vacuum sector is a pure
  -- constant action; use VacuumConstantEncodingReceipt for that source claim.
  sourceNativeAmplitudeReceiptFromProjectedVacua :
    (interiorScale exteriorScale : Nat) →
    localizedVacuumValue interiorScale ≡ Int.+ 21 / 64 →
    localizedVacuumValue exteriorScale ≡ Int.+ 19 / 48 →
    Vacuum.SourceNativeNambuVacuumAmplitudeReceipt source
  sourceNativeAmplitudeReceiptFromProjectedVacua
      interiorScale exteriorScale interior exterior = record
    { Vacuum.SourceNativeNambuVacuumAmplitudeReceipt.readout =
        localizedVacuumConstantReadout
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
    localizedVacuumCarrierHasConstantCoordinate : Bool
    constantRemainderReadoutUsed : Bool
    plaquetteProjectorIsNotVacuumConstantReadout : Bool
    publishedVacuumConstantEncodingStillRequired : Bool
    independentArbitraryVacuumToRatMapRequired : Bool
    twoHistoricalTargetAmplitudeEqualitiesStillRequiredIfNambuRouteUsed : Bool

canonicalLocalizedVacuumReadoutBoundary : LocalizedVacuumReadoutBoundary
canonicalLocalizedVacuumReadoutBoundary =
  localized-vacuum-readout-boundary
    true true true true false true

plaquetteProjectorIsNotVacuumConstantReadout : Bool
plaquetteProjectorIsNotVacuumConstantReadout = true

publishedVacuumConstantEncodingStillRequired : Bool
publishedVacuumConstantEncodingStillRequired = true

constantRemainderCoordinateIsPreferredVacuumReadout : Bool
constantRemainderCoordinateIsPreferredVacuumReadout = true

-- Compatibility exports for older static contracts.  Their values now reflect
-- the corrected constant-coordinate semantics rather than the old projector
-- interpretation.
independentVacuumReadoutStillRequired : Bool
independentVacuumReadoutStillRequired = false

twoSourceAmplitudeEqualitiesStillRequired : Bool
twoSourceAmplitudeEqualitiesStillRequired = true
