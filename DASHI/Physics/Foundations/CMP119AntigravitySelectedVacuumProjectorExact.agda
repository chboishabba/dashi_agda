{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravitySelectedVacuumProjectorExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ)

import DASHI.Physics.YangMills.BalabanCMP119Section2SourceNativeStateExact as CMP119
import DASHI.Physics.YangMills.BalabanClayT4LocalizedPlaquetteCoefficientProducerExact as T4

------------------------------------------------------------------------
-- SELECTED CMP119 VACUUM READOUT: REUSE THE EXISTING ACTION PROJECTOR
--
-- On the selected Eq.(2.23) realization already used by the antigravity
-- source lane, Action/Wilson/E/R/B/Vacuum are all T4.LocalizedAction.  The
-- repository already owns
--
--   plaquetteCoefficientProjector : LocalizedAction -> Q.
--
-- Therefore the literal source vacuum term already has a canonical rational
-- projection.  No second abstract Vacuum -> Q callback is required on this
-- selected route.
------------------------------------------------------------------------

module _
  {Density Background Fluctuation : Set}
  (source : CMP119.CMP119Section2SourceNativeState
    Density Background Fluctuation
    T4.LocalizedAction T4.LocalizedAction T4.LocalizedAction
    T4.LocalizedAction T4.LocalizedAction T4.LocalizedAction)
  where

  selectedVacuumAmplitude : Nat → ℚ
  selectedVacuumAmplitude scale =
    T4.plaquetteCoefficientProjector
      (CMP119.vacuumEnergy source scale)

  selectedVacuumAmplitudeIsLiteralEq223VacuumProjector :
    ∀ scale →
    selectedVacuumAmplitude scale
      ≡ T4.plaquetteCoefficientProjector
          (CMP119.vacuumEnergy source scale)
  selectedVacuumAmplitudeIsLiteralEq223VacuumProjector scale = refl

  record SelectedVacuumAmplitudePair
      (interiorScale exteriorScale : Nat) : Set where
    constructor selected-vacuum-amplitude-pair
    field
      interiorAmplitude : ℚ
      exteriorAmplitude : ℚ
      interiorIsLiteralSourceVacuum :
        interiorAmplitude ≡ selectedVacuumAmplitude interiorScale
      exteriorIsLiteralSourceVacuum :
        exteriorAmplitude ≡ selectedVacuumAmplitude exteriorScale

  open SelectedVacuumAmplitudePair public

  selectedVacuumAmplitudePair :
    (interiorScale exteriorScale : Nat) →
    SelectedVacuumAmplitudePair interiorScale exteriorScale
  selectedVacuumAmplitudePair interiorScale exteriorScale =
    selected-vacuum-amplitude-pair
      (selectedVacuumAmplitude interiorScale)
      (selectedVacuumAmplitude exteriorScale)
      refl refl

record SelectedVacuumProjectorBoundary : Set where
  constructor selected-vacuum-projector-boundary
  field
    selectedVacuumCarrierIsLocalizedAction : Bool
    existingPlaquetteProjectorReused : Bool
    selectedVacuumAmplitudeIsSourceNative : Bool
    noIndependentVacuumReadoutRequired : Bool
    oldArbitraryVacuumToRatCallbackRequired : Bool
    sourceScaleValuesStillMustBeEvaluatedOrBounded : Bool

canonicalSelectedVacuumProjectorBoundary : SelectedVacuumProjectorBoundary
canonicalSelectedVacuumProjectorBoundary =
  selected-vacuum-projector-boundary
    true true true true false true
