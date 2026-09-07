module DASHI.Physics.GR.GravitationalObservationBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Physics.GR.GravitationalObservationSourceAtlasExact as Sources

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
    attributedObservationSource : Sources.ObservationAttributedSource
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
    attributedObservationCarrierRequired : Bool
    positiveStatusNeedsSourceEntitledClaim : Bool
    observationMayConstrainModifiedGravity : Bool
    observationAutomaticallyPromotesModifiedGravity : Bool

canonicalGravitationalObservationBoundary : GravitationalObservationBoundary
canonicalGravitationalObservationBoundary =
  gravitational-observation-boundary
    false false false false true true true true true false

data ObservationResidual : Set where
  missingAttributedCarrier : ObservationResidual
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
    attributedCarrierRequired : Bool
    calibrationRequired : Bool
    noiseModelRequired : Bool
    sourceComparatorRequired : Bool
    exactRevisionRequired : Bool

laserInterferometerCutset : ObservationReverseCutset
laserInterferometerCutset =
  observation-reverse-cutset
    laserInterferometricStrain dimensionlessStrain refl true true true true true

pulsarTimingCutset : ObservationReverseCutset
pulsarTimingCutset =
  observation-reverse-cutset
    pulsarTimingResidual correlatedArrivalTimeResidual refl true true true true true

laserAndPulsarObservablesDistinct :
  observableFor laserInterferometricStrain ≡ observableFor pulsarTimingResidual → ⊥
laserAndPulsarObservablesDistinct ()

freeFallAndStrainObservablesDistinct :
  observableFor freeFallEquivalence ≡ observableFor laserInterferometricStrain → ⊥
freeFallAndStrainObservablesDistinct ()

------------------------------------------------------------------------
-- Positive current status is represented by source-entitled claim receipts.
-- Negative promotion statements remain DASHI boundary judgments.
------------------------------------------------------------------------

record CurrentObservationalStatusBoundary : Set where
  constructor current-observational-status-boundary
  field
    compactBinaryCatalogClaim :
      Sources.SourceEntitledObservationClaim
        Sources.gwtc5CompactBinaryCatalogClaim
    nanohertzBackgroundEvidenceClaim :
      Sources.SourceEntitledObservationClaim
        Sources.nanoGravBackgroundEvidenceClaim
    currentGRTestSuiteClaim :
      Sources.SourceEntitledObservationClaim
        Sources.lvkCurrentGRTestSuiteClaim
    allObservedSignalsRequireBeyondGR : Bool
    observationLayerProvesAntigravity : Bool

canonicalCurrentObservationalStatusBoundary : CurrentObservationalStatusBoundary
canonicalCurrentObservationalStatusBoundary =
  current-observational-status-boundary
    (Sources.canonicalSourceEntitledClaim Sources.gwtc5CompactBinaryCatalogClaim)
    (Sources.canonicalSourceEntitledClaim Sources.nanoGravBackgroundEvidenceClaim)
    (Sources.canonicalSourceEntitledClaim Sources.lvkCurrentGRTestSuiteClaim)
    false false

sourceBoundary : Sources.GravitationalObservationSourceBoundary
sourceBoundary = Sources.canonicalGravitationalObservationSourceBoundary
