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

------------------------------------------------------------------------
-- Field-induced antenna support.  Darshni, Dogariu, Franzon (2026).
-- IEEE Journal of Microwaves 6(5), 1174-1183.
-- DOI: 10.1109/JMW.2026.3722433.
-- The 30 MHz experiment is near-field.  It does not prove far-field gain.
-- This is a finite classification theorem, not a plasma Maxwell solver.
------------------------------------------------------------------------

data ApertureSupportMode : Set where
  fixedMaterialSupport : ApertureSupportMode
  electronicallyWeightedSupport : ApertureSupportMode
  laserInducedPlasmaSupport : ApertureSupportMode

laserSupportIsNotElectronicWeighting :
  laserInducedPlasmaSupport ≡ electronicallyWeightedSupport → ⊥
laserSupportIsNotElectronicWeighting ()

laserSupportIsNotFixedMaterial :
  laserInducedPlasmaSupport ≡ fixedMaterialSupport → ⊥
laserSupportIsNotFixedMaterial ()

data PlasmaAntennaClaim : Set where
  measuredNearFieldContrast : PlasmaAntennaClaim
  demonstratedFarFieldGain : PlasmaAntennaClaim
  demonstratedReception : PlasmaAntennaClaim
  demonstratedBroadbandOperation : PlasmaAntennaClaim

nearFieldContrastIsNotFarFieldGain :
  measuredNearFieldContrast ≡ demonstratedFarFieldGain → ⊥
nearFieldContrastIsNotFarFieldGain ()

nearFieldContrastIsNotReception :
  measuredNearFieldContrast ≡ demonstratedReception → ⊥
nearFieldContrastIsNotReception ()

nearFieldContrastIsNotBroadbandProof :
  measuredNearFieldContrast ≡ demonstratedBroadbandOperation → ⊥
nearFieldContrastIsNotBroadbandProof ()
