module DASHI.Statistics.ForecastCalibrationDecompositionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _≤_; _<_)

import DASHI.Statistics.ForecastVerificationKernelExact as Kernel
import DASHI.Statistics.ForecastResolutionSelectionExact as Lifecycle

------------------------------------------------------------------------
-- CALIBRATION / DECOMPOSITION / COMPARATOR COORDINATES
--
-- A single proper score is not a complete representation of forecast quality.
-- These records retain the coordinates needed to explain the same scalar score
-- by different calibration, discrimination/resolution, coverage and selection
-- structures.
------------------------------------------------------------------------

record CalibrationBucket : Set where
  constructor calibration-bucket
  field
    bucketReference : String
    forecastCount : Nat
    averagePredicted : ℚ
    observedFrequency : ℚ
    bucketBrier : ℚ
    nonemptyReference : String

open CalibrationBucket public

data BucketObservation : Set where
  emptyBucket : String → BucketObservation
  populatedBucket : CalibrationBucket → BucketObservation

record BrierDecompositionReceipt : Set where
  constructor brier-decomposition-receipt
  field
    score : ℚ
    reliability : ℚ
    resolution : ℚ
    uncertainty : ℚ
    partitionReference : String
    cohortReference : String

    reconstructsScore :
      score ≡ reliability - resolution + uncertainty

open BrierDecompositionReceipt public

record ForecastQualityVector : Set where
  constructor forecast-quality-vector
  field
    properScoreReference : String
    calibrationReference : String
    discriminationReference : String
    coverageReference : String
    scorabilityReference : String
    cohortStabilityReference : String
    temporalStabilityReference : String

open ForecastQualityVector public

------------------------------------------------------------------------
-- Reference models / base-rate contextualisation.
------------------------------------------------------------------------

data ReferenceForecastKind : Set where
  constantHalf
  cohortBaseRate
  historicalRollingBaseRate
  marketComparator
  declaredSimpleModel :
    ReferenceForecastKind

record ReferenceForecastReceipt : Set where
  constructor reference-forecast-receipt
  field
    kind : ReferenceForecastKind
    cohortReference : String
    informationCutReference : String
    score : ℚ
    referenceModelReference : String

open ReferenceForecastReceipt public

record ForecastSkillAgainstReference : Set where
  constructor forecast-skill-against-reference
  field
    forecastScore : ℚ
    reference : ReferenceForecastReceipt
    referenceScorePositive : 0ℚ < score reference
    skillCoordinate : ℚ

    -- Division-free form of skill = 1 - forecast/reference:
    -- (1 - skill) * reference = forecast.
    skillReconstructs :
      (1ℚ - skillCoordinate) * score reference ≡ forecastScore

    skillFormulaReference : String
    betterThanReferenceCreatesAbsoluteQuality : Bool
    betterThanReferenceCreatesAbsoluteQualityIsFalse :
      betterThanReferenceCreatesAbsoluteQuality ≡ false

open ForecastSkillAgainstReference public

------------------------------------------------------------------------
-- Paired forecast comparison.
------------------------------------------------------------------------

record PairedForecastComparison : Set where
  constructor paired-forecast-comparison
  field
    questionReference : String
    leftProbability : Kernel.Probability
    rightProbability : Kernel.Probability
    outcome : Kernel.BinaryOutcome
    leftBrier : ℚ
    rightBrier : ℚ
    deltaRightMinusLeft : ℚ

    leftLossCorrect :
      leftBrier ≡ Kernel.brierLoss leftProbability outcome

    rightLossCorrect :
      rightBrier ≡ Kernel.brierLoss rightProbability outcome

    deltaCorrect :
      deltaRightMinusLeft ≡ rightBrier - leftBrier

    pairedCarrierReference : String

open PairedForecastComparison public

record PairedComparisonAggregateReceipt : Set where
  constructor paired-comparison-aggregate-receipt
  field
    pairedQuestionCount : Nat
    leftAggregateScore : ℚ
    rightAggregateScore : ℚ
    aggregateDeltaRightMinusLeft : ℚ
    pairingReference : String
    uncertaintyReference : String
    domainStrataReference : String
    confidenceStrataReference : String

open PairedComparisonAggregateReceipt public

------------------------------------------------------------------------
-- Scalar-score collision: same score need not mean same mechanism.
------------------------------------------------------------------------

data ErrorMechanism : Set where
  calibrationError
  discriminationError
  representationError
  temporalRegimeError
  sourceEvidenceError
  resolutionObserverError :
    ErrorMechanism

record SameScoreDifferentMechanism : Set where
  constructor same-score-different-mechanism
  field
    leftMechanism rightMechanism : ErrorMechanism
    leftScore rightScore : ℚ
    sameScore : leftScore ≡ rightScore
    differentMechanismReference : String

open SameScoreDifferentMechanism public

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record ForecastCalibrationBoundary : Set where
  constructor forecast-calibration-boundary
  field
    emptyBucketEqualsZeroObservation : Bool
    emptyBucketEqualsZeroObservationIsFalse :
      emptyBucketEqualsZeroObservation ≡ false

    brierAloneIsCompleteForecastQuality : Bool
    brierAloneIsCompleteForecastQualityIsFalse :
      brierAloneIsCompleteForecastQuality ≡ false

    bucketCalibrationIsIndividualCorpus : Bool
    bucketCalibrationIsIndividualCorpusIsFalse :
      bucketCalibrationIsIndividualCorpus ≡ false

    pairedSampleAdvantageIsUniversalAdvantage : Bool
    pairedSampleAdvantageIsUniversalAdvantageIsFalse :
      pairedSampleAdvantageIsUniversalAdvantage ≡ false

    sameScoreImpliesSameErrorMechanism : Bool
    sameScoreImpliesSameErrorMechanismIsFalse :
      sameScoreImpliesSameErrorMechanism ≡ false

canonicalForecastCalibrationBoundary : ForecastCalibrationBoundary
canonicalForecastCalibrationBoundary =
  forecast-calibration-boundary
    false refl
    false refl
    false refl
    false refl
    false refl
