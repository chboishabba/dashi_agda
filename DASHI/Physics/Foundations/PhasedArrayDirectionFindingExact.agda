module DASHI.Physics.Foundations.PhasedArrayDirectionFindingExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- Separate physical support geometry from electronically selected beam
-- geometry.  This is a bounded observation model, not a radar-control or
-- targeting implementation.
------------------------------------------------------------------------

data ArrayImplementation : Set where
  mechanicallySteeredAntenna : ArrayImplementation
  phaseComparisonInterferometer : ArrayImplementation
  electronicallySteeredPhasedArray : ArrayImplementation
  monopulseArray : ArrayImplementation
  digitalBeamformingArray : ArrayImplementation

data ArrayObservationCoordinate : Set where
  carrierOrientation : ArrayObservationCoordinate
  arrayFaceOrientation : ArrayObservationCoordinate
  electronicSteeringCoordinate : ArrayObservationCoordinate
  relativePhaseCoordinate : ArrayObservationCoordinate
  relativeAmplitudeCoordinate : ArrayObservationCoordinate

data ArrayRole : Set where
  angularObservationRole : ArrayRole
  beamSteeringRole : ArrayRole

supportsAngularObservation : ArrayImplementation → ArrayRole
supportsAngularObservation mechanicallySteeredAntenna = angularObservationRole
supportsAngularObservation phaseComparisonInterferometer = angularObservationRole
supportsAngularObservation electronicallySteeredPhasedArray = angularObservationRole
supportsAngularObservation monopulseArray = angularObservationRole
supportsAngularObservation digitalBeamformingArray = angularObservationRole

physicalOrientationIsNotElectronicSteering :
  arrayFaceOrientation ≡ electronicSteeringCoordinate → ⊥
physicalOrientationIsNotElectronicSteering ()

phaseCoordinateIsNotAmplitudeCoordinate :
  relativePhaseCoordinate ≡ relativeAmplitudeCoordinate → ⊥
phaseCoordinateIsNotAmplitudeCoordinate ()

------------------------------------------------------------------------
-- Array-derived bearing remains a projection of a richer emitter world.
------------------------------------------------------------------------

data ArrayBearing : Set where
  bearingA : ArrayBearing
  bearingB : ArrayBearing

data ArrayEmitterWorld : Set where
  nearA : ArrayEmitterWorld
  farA : ArrayEmitterWorld
  worldB : ArrayEmitterWorld

observeArrayBearing : ArrayEmitterWorld → ArrayBearing
observeArrayBearing nearA = bearingA
observeArrayBearing farA = bearingA
observeArrayBearing worldB = bearingB

nearAndFarArrayWorldsDistinct : nearA ≡ farA → ⊥
nearAndFarArrayWorldsDistinct ()

ArrayBearingDeterminesExactEmitterWorld : Set
ArrayBearingDeterminesExactEmitterWorld =
  (x y : ArrayEmitterWorld) →
  observeArrayBearing x ≡ observeArrayBearing y →
  x ≡ y

arrayBearingDoesNotDetermineExactEmitterWorld :
  ¬ ArrayBearingDeterminesExactEmitterWorld
arrayBearingDoesNotDetermineExactEmitterWorld exact =
  nearAndFarArrayWorldsDistinct (exact nearA farA refl)

record SameArrayBearingCollision : Set where
  constructor same-array-bearing-collision
  field
    leftWorld : ArrayEmitterWorld
    rightWorld : ArrayEmitterWorld
    sameBearing : observeArrayBearing leftWorld ≡ observeArrayBearing rightWorld
    differentWorld : leftWorld ≡ rightWorld → ⊥

open SameArrayBearingCollision public

canonicalSameArrayBearingCollision : SameArrayBearingCollision
canonicalSameArrayBearingCollision =
  same-array-bearing-collision nearA farA refl nearAndFarArrayWorldsDistinct

------------------------------------------------------------------------
-- Sharing phase coordinates does not identify steering with direction finding.
------------------------------------------------------------------------

record SteeringDFFirewall : Set where
  constructor steering-df-firewall
  field
    phasedArrayCanUseRelativePhase : Bool
    phasedArrayCanUseRelativePhaseIsTrue : phasedArrayCanUseRelativePhase ≡ true
    directionFindingCanUseRelativePhase : Bool
    directionFindingCanUseRelativePhaseIsTrue : directionFindingCanUseRelativePhase ≡ true
    sharedPhaseCoordinateImpliesSameOperation : Bool
    sharedPhaseCoordinateImpliesSameOperationIsFalse :
      sharedPhaseCoordinateImpliesSameOperation ≡ false

open SteeringDFFirewall public

canonicalSteeringDFFirewall : SteeringDFFirewall
canonicalSteeringDFFirewall =
  steering-df-firewall true refl true refl false refl
