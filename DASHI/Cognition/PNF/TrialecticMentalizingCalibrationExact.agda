module DASHI.Cognition.PNF.TrialecticMentalizingCalibrationExact where

------------------------------------------------------------------------
-- MENTALIZING / MODEL CALIBRATION NON-COLLAPSE
--
-- SOURCE / ATTRIBUTION BOUNDARY
--
-- The source atlas motivates keeping self/other mentalizing, model activity,
-- accuracy, confidence and calibration distinct.  The finite collision
-- witnesses below are DASHI theorems.  No source citation proves these
-- factorization failures, and this module is not a diagnostic instrument.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent
import DASHI.Core.RelationalTrialecticSourceAtlasExact as Sources

data CapacityLevel : Set where
  lowCapacity : CapacityLevel
  mediumCapacity : CapacityLevel
  highCapacity : CapacityLevel

data ActivityLevel : Set where
  lowActivity : ActivityLevel
  highActivity : ActivityLevel

data AccuracyLevel : Set where
  lowAccuracy : AccuracyLevel
  highAccuracy : AccuracyLevel

data ConfidenceLevel : Set where
  lowConfidence : ConfidenceLevel
  highConfidence : ConfidenceLevel

data CalibrationLevel : Set where
  poorCalibration : CalibrationLevel
  goodCalibration : CalibrationLevel

data AuthorityLevel : Set where
  lowSelfAuthority : AuthorityLevel
  highSelfAuthority : AuthorityLevel

record MentalizingCalibrationState : Set where
  constructor mentalizing-calibration-state
  field
    selfMentalizing : CapacityLevel
    otherMentalizing : CapacityLevel
    modelActivity : ActivityLevel
    modelAccuracy : AccuracyLevel
    modelConfidence : ConfidenceLevel
    modelCalibration : CalibrationLevel
    selfAuthority : AuthorityLevel

open MentalizingCalibrationState public

data CalibrationEpisode : Set where
  highActivityAccurate : CalibrationEpisode
  highActivityInaccurate : CalibrationEpisode
  highConfidenceCalibrated : CalibrationEpisode
  highConfidenceMiscalibrated : CalibrationEpisode
  highMonitoringLowAuthority : CalibrationEpisode
  highMonitoringHighAuthority : CalibrationEpisode

activityObserver : CalibrationEpisode → ActivityLevel
activityObserver highActivityAccurate = highActivity
activityObserver highActivityInaccurate = highActivity
activityObserver _ = lowActivity

accuracyConsumer : CalibrationEpisode → AccuracyLevel
accuracyConsumer highActivityAccurate = highAccuracy
accuracyConsumer highActivityInaccurate = lowAccuracy
accuracyConsumer _ = lowAccuracy

confidenceObserver : CalibrationEpisode → ConfidenceLevel
confidenceObserver highConfidenceCalibrated = highConfidence
confidenceObserver highConfidenceMiscalibrated = highConfidence
confidenceObserver _ = lowConfidence

calibrationConsumer : CalibrationEpisode → CalibrationLevel
calibrationConsumer highConfidenceCalibrated = goodCalibration
calibrationConsumer highConfidenceMiscalibrated = poorCalibration
calibrationConsumer _ = poorCalibration

monitoringObserver : CalibrationEpisode → CapacityLevel
monitoringObserver highMonitoringLowAuthority = highCapacity
monitoringObserver highMonitoringHighAuthority = highCapacity
monitoringObserver _ = lowCapacity

authorityConsumer : CalibrationEpisode → AuthorityLevel
authorityConsumer highMonitoringLowAuthority = lowSelfAuthority
authorityConsumer highMonitoringHighAuthority = highSelfAuthority
authorityConsumer _ = lowSelfAuthority

activityAccuracyWitness :
  Descent.ConsumerNonDescentWitness activityObserver accuracyConsumer
activityAccuracyWitness =
  Descent.consumerNonDescentWitness
    highActivityAccurate
    highActivityInaccurate
    refl
    (λ ())

modelAccuracyDoesNotFactorThroughActivity :
  Descent.FactorsThrough activityObserver accuracyConsumer → ⊥
modelAccuracyDoesNotFactorThroughActivity =
  Descent.nonDescentWitnessBlocksFactorization activityAccuracyWitness

confidenceCalibrationWitness :
  Descent.ConsumerNonDescentWitness confidenceObserver calibrationConsumer
confidenceCalibrationWitness =
  Descent.consumerNonDescentWitness
    highConfidenceCalibrated
    highConfidenceMiscalibrated
    refl
    (λ ())

calibrationDoesNotFactorThroughConfidence :
  Descent.FactorsThrough confidenceObserver calibrationConsumer → ⊥
calibrationDoesNotFactorThroughConfidence =
  Descent.nonDescentWitnessBlocksFactorization confidenceCalibrationWitness

monitoringAuthorityWitness :
  Descent.ConsumerNonDescentWitness monitoringObserver authorityConsumer
monitoringAuthorityWitness =
  Descent.consumerNonDescentWitness
    highMonitoringLowAuthority
    highMonitoringHighAuthority
    refl
    (λ ())

selfAuthorityDoesNotFactorThroughOtherMonitoring :
  Descent.FactorsThrough monitoringObserver authorityConsumer → ⊥
selfAuthorityDoesNotFactorThroughOtherMonitoring =
  Descent.nonDescentWitnessBlocksFactorization monitoringAuthorityWitness

data SelfMentalizingEqualsOtherMentalizing : Set where
data MoreModelActivityMeansMoreAccuracy : Set where
data MoreConfidenceMeansBetterCalibration : Set where
data HighOtherMonitoringMeansHighSelfAuthority : Set where

selfMentalizingIsNotDefinitionallyOtherMentalizing :
  SelfMentalizingEqualsOtherMentalizing → ⊥
selfMentalizingIsNotDefinitionallyOtherMentalizing ()

modelActivityIsNotAccuracy :
  MoreModelActivityMeansMoreAccuracy → ⊥
modelActivityIsNotAccuracy ()

confidenceIsNotCalibration :
  MoreConfidenceMeansBetterCalibration → ⊥
confidenceIsNotCalibration ()

otherMonitoringIsNotSelfAuthority :
  HighOtherMonitoringMeansHighSelfAuthority → ⊥
otherMonitoringIsNotSelfAuthority ()

record TrialecticMentalizingCalibrationBoundary : Set where
  constructor trialectic-mentalizing-calibration-boundary
  field
    selfAndOtherMentalizingAreSeparateCoordinates : Bool
    highModelActivityGuaranteesAccuracy : Bool
    highConfidenceGuaranteesCalibration : Bool
    highOtherMonitoringGuaranteesSelfAuthority : Bool
    hypermentalizingSourceCreatesDiagnosis : Bool
    psychometricMeasureDefinesFineOntology : Bool

canonicalTrialecticMentalizingCalibrationBoundary :
  TrialecticMentalizingCalibrationBoundary
canonicalTrialecticMentalizingCalibrationBoundary =
  trialectic-mentalizing-calibration-boundary
    true false false false false false
