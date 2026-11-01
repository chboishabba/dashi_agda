module DASHI.Biology.AvianMagnetoreceptionRFAngularObservationQuotientExact where

open import DASHI.Core.Prelude

import DASHI.Biology.AvianMagnetoreceptionFieldObservationQuotientExact as BioField
import DASHI.Physics.Foundations.RadioRadarGoniometerDirectionFindingExact as Goniometer
import DASHI.Physics.Foundations.PhasedArrayDirectionFindingExact as Array
import DASHI.Physics.Foundations.RFSensingThroughWallExact as RF

------------------------------------------------------------------------
-- Same inverse-problem shape, distinct physical domains.
--
-- goniometer bearing       -> not exact emitter world
-- phased-array bearing     -> not exact emitter world
-- RF observation           -> not exact human world
-- chamber field readout    -> not exact receptor-exposure world
--
-- The theorem is about shared observation-quotient structure only.  It does
-- not identify the underlying hardware, carriers, or physics.
------------------------------------------------------------------------

record SharedObservationQuotientWitness : Set where
  constructor shared-observation-quotient-witness
  field
    goniometerNonInjective :
      ¬ Goniometer.BearingDeterminesExactEmitterWorld

    phasedArrayNonInjective :
      ¬ Array.ArrayBearingDeterminesExactEmitterWorld

    rfSensingNonInjective :
      ¬ RF.RFObservationDeterminesExactHumanWorld

    chamberFieldNonInjective :
      ¬ BioField.ChamberMeasurementDeterminesExactReceptorExposure

    commandSynthesisNonInjective :
      ¬ BioField.CommandDeterminesExactGeneratedField

open SharedObservationQuotientWitness public

canonicalSharedObservationQuotientWitness :
  SharedObservationQuotientWitness
canonicalSharedObservationQuotientWitness =
  shared-observation-quotient-witness
    Goniometer.bearingDoesNotDetermineExactEmitterWorld
    Array.arrayBearingDoesNotDetermineExactEmitterWorld
    RF.rfObservationDoesNotDetermineExactHumanWorld
    BioField.chamberMeasurementDoesNotDetermineExactReceptorExposure
    BioField.commandDoesNotDetermineExactGeneratedField

record SharedObservationQuotientBoundary : Set where
  constructor shared-observation-quotient-boundary
  field
    commonNonInjectiveShape : Bool
    commonNonInjectiveShapeIsTrue :
      commonNonInjectiveShape ≡ true

    commonShapeImpliesSamePhysics : Bool
    commonShapeImpliesSamePhysicsIsFalse :
      commonShapeImpliesSamePhysics ≡ false

    commonShapeImpliesSameHardware : Bool
    commonShapeImpliesSameHardwareIsFalse :
      commonShapeImpliesSameHardware ≡ false

    inverseObservationSupportsMechanismIdentity : Bool
    inverseObservationSupportsMechanismIdentityIsFalse :
      inverseObservationSupportsMechanismIdentity ≡ false

canonicalSharedObservationQuotientBoundary :
  SharedObservationQuotientBoundary
canonicalSharedObservationQuotientBoundary =
  shared-observation-quotient-boundary
    true refl
    false refl
    false refl
    false refl
