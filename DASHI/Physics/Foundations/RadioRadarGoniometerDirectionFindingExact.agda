module DASHI.Physics.Foundations.RadioRadarGoniometerDirectionFindingExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- A bounded formal model of the angle-measurement role shared by historical
-- radio-direction-finding goniometers and several later electronic angle
-- estimation implementations.  This module does not model an operational
-- targeting chain, emitter geolocation procedure, or weapon employment.

data DirectionFindingImplementation : Set where
  mechanicalAngleReadout : DirectionFindingImplementation
  phaseComparison : DirectionFindingImplementation
  amplitudeComparison : DirectionFindingImplementation
  monopulse : DirectionFindingImplementation
  digitalBeamforming : DirectionFindingImplementation

data AngleMeasurementRole : Set where
  angleEstimationRole : AngleMeasurementRole

implementationRole :
  DirectionFindingImplementation → AngleMeasurementRole
implementationRole _ = angleEstimationRole

allImplementationsShareAngleMeasurementRole :
  (x : DirectionFindingImplementation) →
  implementationRole x ≡ angleEstimationRole
allImplementationsShareAngleMeasurementRole _ = refl

mechanicalAngleReadoutIsNotPhaseComparison :
  mechanicalAngleReadout ≡ phaseComparison → ⊥
mechanicalAngleReadoutIsNotPhaseComparison ()

mechanicalAngleReadoutIsNotDigitalBeamforming :
  mechanicalAngleReadout ≡ digitalBeamforming → ⊥
mechanicalAngleReadoutIsNotDigitalBeamforming ()

------------------------------------------------------------------------
-- Observation is deliberately coarser than the emitting world.

data BearingObservation : Set where
  bearingNorthEast : BearingObservation
  bearingSouthWest : BearingObservation

data EmitterWorld : Set where
  nearEmitterNorthEast : EmitterWorld
  farEmitterNorthEast : EmitterWorld
  emitterSouthWest : EmitterWorld

observeBearing : EmitterWorld → BearingObservation
observeBearing nearEmitterNorthEast = bearingNorthEast
observeBearing farEmitterNorthEast = bearingNorthEast
observeBearing emitterSouthWest = bearingSouthWest

nearAndFarWorldsShareBearing :
  observeBearing nearEmitterNorthEast
  ≡ observeBearing farEmitterNorthEast
nearAndFarWorldsShareBearing = refl

nearAndFarWorldsDistinct :
  nearEmitterNorthEast ≡ farEmitterNorthEast → ⊥
nearAndFarWorldsDistinct ()

BearingDeterminesExactEmitterWorld : Set
BearingDeterminesExactEmitterWorld =
  (x y : EmitterWorld) →
  observeBearing x ≡ observeBearing y →
  x ≡ y

bearingDoesNotDetermineExactEmitterWorld :
  ¬ BearingDeterminesExactEmitterWorld
bearingDoesNotDetermineExactEmitterWorld exact =
  nearAndFarWorldsDistinct
    (exact nearEmitterNorthEast farEmitterNorthEast refl)

record SameBearingCollision : Set where
  constructor same-bearing-collision
  field
    leftWorld : EmitterWorld
    rightWorld : EmitterWorld
    sameBearing : observeBearing leftWorld ≡ observeBearing rightWorld
    differentWorld : leftWorld ≡ rightWorld → ⊥

open SameBearingCollision public

canonicalSameBearingCollision : SameBearingCollision
canonicalSameBearingCollision =
  same-bearing-collision
    nearEmitterNorthEast
    farEmitterNorthEast
    refl
    nearAndFarWorldsDistinct

------------------------------------------------------------------------
-- Keep observation, identification, and authority on separate carriers.

data DirectionFindingObservation : Set where
  boundedBearingObserved : DirectionFindingObservation

data DirectionFindingIdentification : Set where
  boundedDirectionHypothesis : DirectionFindingIdentification

data DirectionFindingPolicy : Set where
  militaryActionAuthorised : DirectionFindingPolicy

record DirectionFindingBoundary : Set where
  constructor direction-finding-boundary
  field
    bearingDeterminesExactEmitterPosition : Bool
    bearingDeterminesExactEmitterPositionIsFalse :
      bearingDeterminesExactEmitterPosition ≡ false

    bearingDeterminesExactEmitterIdentity : Bool
    bearingDeterminesExactEmitterIdentityIsFalse :
      bearingDeterminesExactEmitterIdentity ≡ false

    goniometerNameDeterminesHardwareImplementation : Bool
    goniometerNameDeterminesHardwareImplementationIsFalse :
      goniometerNameDeterminesHardwareImplementation ≡ false

    goniometricObservationAuthorisesMilitaryAction : Bool
    goniometricObservationAuthorisesMilitaryActionIsFalse :
      goniometricObservationAuthorisesMilitaryAction ≡ false

open DirectionFindingBoundary public

canonicalDirectionFindingBoundary : DirectionFindingBoundary
canonicalDirectionFindingBoundary =
  direction-finding-boundary
    false refl
    false refl
    false refl
    false refl

------------------------------------------------------------------------
-- The role is intentionally weaker than any claim of hardware identity.
-- Historical mechanical RDF and later phase/amplitude/monopulse/digital
-- implementations may all instantiate angle estimation while remaining
-- distinct implementations.

record GoniometerRoleFirewall : Set where
  constructor goniometer-role-firewall
  field
    mechanicalCarriesAngleRole :
      implementationRole mechanicalAngleReadout ≡ angleEstimationRole
    phaseCarriesAngleRole :
      implementationRole phaseComparison ≡ angleEstimationRole
    amplitudeCarriesAngleRole :
      implementationRole amplitudeComparison ≡ angleEstimationRole
    monopulseCarriesAngleRole :
      implementationRole monopulse ≡ angleEstimationRole
    beamformingCarriesAngleRole :
      implementationRole digitalBeamforming ≡ angleEstimationRole
    commonRoleImpliesSameImplementation : Bool
    commonRoleImpliesSameImplementationIsFalse :
      commonRoleImpliesSameImplementation ≡ false

canonicalGoniometerRoleFirewall : GoniometerRoleFirewall
canonicalGoniometerRoleFirewall =
  goniometer-role-firewall
    refl refl refl refl refl
    false refl
