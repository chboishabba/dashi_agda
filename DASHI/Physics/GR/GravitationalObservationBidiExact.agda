module DASHI.Physics.GR.GravitationalObservationBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- GRAVITATIONAL OBSERVATION AS A TYPED EVIDENCE LAYER
--
-- Gravitational observation is not represented by one generic "gravity seen"
-- bit.  Detector families expose different observables and therefore pay
-- different reverse obligations.
------------------------------------------------------------------------

data GravitationalObservationChannel : Set where
  laserInterferometricStrain : GravitationalObservationChannel
  pulsarTimingResidual : GravitationalObservationChannel
  orbitalDecayTiming : GravitationalObservationChannel
  freeFallEquivalence : GravitationalObservationChannel
  clockOrRedshift : GravitationalObservationChannel
  localTestMassAcceleration : GravitationalObservationChannel

data GravitationalObservable : Set where
  dimensionlessStrain : GravitationalObservable
  correlatedArrivalTimeResidual : GravitationalObservable
  orbitalPeriodDerivative : GravitationalObservable
  differentialAcceleration : GravitationalObservable
  frequencyRatioShift : GravitationalObservable
  localAccelerationResidual : GravitationalObservable

observableFor : GravitationalObservationChannel → GravitationalObservable
observableFor laserInterferometricStrain = dimensionlessStrain
observableFor pulsarTimingResidual = correlatedArrivalTimeResidual
observableFor orbitalDecayTiming = orbitalPeriodDerivative
observableFor freeFallEquivalence = differentialAcceleration
observableFor clockOrRedshift = frequencyRatioShift
observableFor localTestMassAcceleration = localAccelerationResidual

------------------------------------------------------------------------
-- Observation chain.
------------------------------------------------------------------------

record GravitationalObservationReceipt : Set where
  constructor gravitational-observation-receipt
  field
    channel : GravitationalObservationChannel
    observable : GravitationalObservable
    observableMatchesChannel : observableFor channel ≡ observable
    detectorOrClockCarrier : String
    calibrationCarrier : String
    dataRevision : String
    environmentalSubtractionOrNoiseModel : String
    analysisPipeline : String
    sourceModel : String
    exactResultLocator : String

open GravitationalObservationReceipt public

record GravitationalObservationBoundary : Set where
  constructor gravitational-observation-boundary
  field
    rawDetectorOutputIsCalibratedStrain : Bool
    calibratedStrainAloneIdentifiesAstrophysicalSource : Bool
    timingResidualAloneProvesGravitationalWaveBackground : Bool
    waveformAgreementAloneProvesGRUniquelyTrue : Bool
    detectorCalibrationAndNoiseModelRequired : Bool
    independentSourceModelComparisonRequired : Bool
    observationMayConstrainModifiedGravity : Bool
    observationAutomaticallyPromotesModifiedGravity : Bool

canonicalGravitationalObservationBoundary : GravitationalObservationBoundary
canonicalGravitationalObservationBoundary =
  gravitational-observation-boundary
    false false false false true true true false

------------------------------------------------------------------------
-- Reverse obligations by channel.
------------------------------------------------------------------------

data ObservationResidual : Set where
  missingCalibration : ObservationResidual
  missingNoiseCharacterisation : ObservationResidual
  missingCoincidenceOrCorrelation : ObservationResidual
  missingWaveformOrSourceModel : ObservationResidual
  missingDistanceOrSkyConsistency : ObservationResidual
  missingGRComparator : ObservationResidual
  missingAlternativeGravityComparator : ObservationResidual
  missingExactDataRevision : ObservationResidual

record ObservationReverseCutset : Set where
  constructor observation-reverse-cutset
  field
    channel : GravitationalObservationChannel
    requiredPrimaryObservable : GravitationalObservable
    primaryObservableMatches : observableFor channel ≡ requiredPrimaryObservable
    calibrationRequired : Bool
    noiseModelRequired : Bool
    sourceComparatorRequired : Bool
    exactRevisionRequired : Bool

laserInterferometerCutset : ObservationReverseCutset
laserInterferometerCutset =
  observation-reverse-cutset
    laserInterferometricStrain dimensionlessStrain refl true true true true

pulsarTimingCutset : ObservationReverseCutset
pulsarTimingCutset =
  observation-reverse-cutset
    pulsarTimingResidual correlatedArrivalTimeResidual refl true true true true

------------------------------------------------------------------------
-- Detector-family non-collapse.
------------------------------------------------------------------------

laserAndPulsarObservablesDistinct :
  observableFor laserInterferometricStrain ≡ observableFor pulsarTimingResidual → ⊥
laserAndPulsarObservablesDistinct ()

freeFallAndStrainObservablesDistinct :
  observableFor freeFallEquivalence ≡ observableFor laserInterferometricStrain → ⊥
freeFallAndStrainObservablesDistinct ()

record CurrentObservationalStatusBoundary : Set where
  constructor current-observational-status-boundary
  field
    compactBinaryStrainObservationsExist : Bool
    stochasticNanohertzBackgroundEvidenceExists : Bool
    gravitationalWaveObservationsTestGR : Bool
    allObservedSignalsRequireBeyondGR : Bool
    observationLayerProvesAntigravity : Bool

canonicalCurrentObservationalStatusBoundary : CurrentObservationalStatusBoundary
canonicalCurrentObservationalStatusBoundary =
  current-observational-status-boundary true true true false false
