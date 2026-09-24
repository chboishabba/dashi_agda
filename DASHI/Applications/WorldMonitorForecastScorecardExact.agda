module DASHI.Applications.WorldMonitorForecastScorecardExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Integer.Base using (+_)
open import Data.Rational using (ℚ; _/_; _-_)

import DASHI.Applications.CounterUASWorldMonitorEvidenceHealthBridgeExact as Health
import DASHI.Statistics.ForecastVerificationKernelExact as Kernel
import DASHI.Statistics.ForecastResolutionSelectionExact as Lifecycle
import DASHI.Statistics.ForecastCalibrationDecompositionExact as Calibration

------------------------------------------------------------------------
-- WORLD MONITOR FORECAST SCORECARD ADAPTER
--
-- Frozen source snapshot:
--   docs/snapshots/crawlable-live-pulse-2026-09-21.json
--   generated 2026-09-20 06:02:08 UTC
--
-- This module records the aggregate scorecard as a typed application fixture.
-- It does not fabricate the unpublished individual forecast corpus, judge
-- evidence, confidence intervals, or long-horizon validation.
------------------------------------------------------------------------

headlineBrier : ℚ
headlineBrier = (+ 115) / 1000

headlineLogScore : ℚ
headlineLogScore = (+ 369) / 1000

allScoredBrier : ℚ
allScoredBrier = (+ 195) / 1000

marketOverlapForecastBrier : ℚ
marketOverlapForecastBrier = (+ 149) / 1000

marketOverlapMarketBrier : ℚ
marketOverlapMarketBrier = (+ 72) / 1000

marketOverlapDelta : ℚ
marketOverlapDelta = marketOverlapMarketBrier - marketOverlapForecastBrier

headlineCount : Nat
headlineCount = 200

ledgerCount : Nat
ledgerCount = 1058

resolvedCount : Nat
resolvedCount = 862

scoredCount : Nat
scoredCount = 541

voidedCount : Nat
voidedCount = 321

awaitingJudgeCount : Nat
awaitingJudgeCount = 94

stillOpenCount : Nat
stillOpenCount = 102

excludedScoredCount : Nat
excludedScoredCount = 341

marketOverlapCount : Nat
marketOverlapCount = 89

ledgerPartitionExact :
  resolvedCount + awaitingJudgeCount + stillOpenCount ≡ ledgerCount
ledgerPartitionExact = refl

resolvedPartitionExact :
  scoredCount + voidedCount ≡ resolvedCount
resolvedPartitionExact = refl

headlinePlusExcludedExact :
  headlineCount + excludedScoredCount ≡ scoredCount
headlinePlusExcludedExact = refl

------------------------------------------------------------------------
-- Headline origin selection.
------------------------------------------------------------------------

headlineOriginIncluded : Lifecycle.ForecastOrigin → Bool
headlineOriginIncluded Lifecycle.betEngine = false
headlineOriginIncluded Lifecycle.stateDerived = false
headlineOriginIncluded Lifecycle.legacyDetector = true
headlineOriginIncluded Lifecycle.unknownOrigin = true
headlineOriginIncluded Lifecycle.otherOrigin = true

betEngineExcluded :
  headlineOriginIncluded Lifecycle.betEngine ≡ false
betEngineExcluded = refl

stateDerivedExcluded :
  headlineOriginIncluded Lifecycle.stateDerived ≡ false
stateDerivedExcluded = refl

unknownOriginIncluded :
  headlineOriginIncluded Lifecycle.unknownOrigin ≡ true
unknownOriginIncluded = refl

------------------------------------------------------------------------
-- Published calibration buckets are aggregate evidence, not an individual
-- forecast corpus.  Empty buckets remain explicit absence-of-observation.
------------------------------------------------------------------------

bucket0to10 : Calibration.CalibrationBucket
bucket0to10 =
  Calibration.calibration-bucket
    "0%-10%"
    40
    ((+ 60) / 1000)
    ((+ 0) / 1000)
    ((+ 5) / 1000)
    "40 scored forecasts"

bucket10to20 : Calibration.CalibrationBucket
bucket10to20 =
  Calibration.calibration-bucket
    "10%-20%"
    67
    ((+ 142) / 1000)
    ((+ 45) / 1000)
    ((+ 54) / 1000)
    "67 scored forecasts"

bucket20to30 : Calibration.CalibrationBucket
bucket20to30 =
  Calibration.calibration-bucket
    "20%-30%"
    87
    ((+ 254) / 1000)
    ((+ 322) / 1000)
    ((+ 225) / 1000)
    "87 scored forecasts"

bucket30to40 : Calibration.CalibrationBucket
bucket30to40 =
  Calibration.calibration-bucket
    "30%-40%"
    184
    ((+ 352) / 1000)
    ((+ 359) / 1000)
    ((+ 229) / 1000)
    "184 scored forecasts"

bucket40to50 : Calibration.CalibrationBucket
bucket40to50 =
  Calibration.calibration-bucket
    "40%-50%"
    117
    ((+ 412) / 1000)
    ((+ 393) / 1000)
    ((+ 237) / 1000)
    "117 scored forecasts"

bucket50to60 : Calibration.CalibrationBucket
bucket50to60 =
  Calibration.calibration-bucket
    "50%-60%"
    32
    ((+ 531) / 1000)
    ((+ 250) / 1000)
    ((+ 268) / 1000)
    "32 scored forecasts"

bucket60to70 : Calibration.CalibrationBucket
bucket60to70 =
  Calibration.calibration-bucket
    "60%-70%"
    13
    ((+ 640) / 1000)
    ((+ 462) / 1000)
    ((+ 274) / 1000)
    "13 scored forecasts"

bucket70to80 : Calibration.BucketObservation
bucket70to80 = Calibration.emptyBucket "70%-80% omitted because no forecasts scored"

bucket80to90 : Calibration.BucketObservation
bucket80to90 = Calibration.emptyBucket "80%-90% omitted because no forecasts scored"

bucket90to100 : Calibration.CalibrationBucket
bucket90to100 =
  Calibration.calibration-bucket
    "90%-100%"
    1
    ((+ 930) / 1000)
    ((+ 1000) / 1000)
    ((+ 5) / 1000)
    "1 scored forecast"

------------------------------------------------------------------------
-- Integrity receipt.
------------------------------------------------------------------------

record WorldMonitorScorecardIntegrityReceipt : Set where
  constructor world-monitor-scorecard-integrity-receipt
  field
    ledgerPartitionCertified : Bool
    cohortPredicateExplicit : Bool
    cohortCountsReconcile : Bool
    scoringRuleDeclared : Bool
    voidPolicyDeclared : Bool
    resolutionPolicyDeclared : Bool
    originCoverageDeclared : Bool
    horizonCoverageDeclared : Bool
    calibrationReported : Bool
    sampleSizesReported : Bool

    confidenceIntervalsAvailable : Bool
    longHorizonScoringAvailable : Bool
    individualForecastLineagePublished : Bool
    resolutionEvidencePublished : Bool
    judgeInputLineagePublished : Bool
    selectionSensitivityAvailable : Bool
    voidSelectionSensitivityAvailable : Bool
    pairedComparatorUncertaintyAvailable : Bool

    createsForecastTruth : Bool
    createsWorldTruth : Bool

open WorldMonitorScorecardIntegrityReceipt public

canonicalWorldMonitorIntegrity :
  WorldMonitorScorecardIntegrityReceipt
canonicalWorldMonitorIntegrity =
  world-monitor-scorecard-integrity-receipt
    true true true true true true true true true true
    false false false false false false false false
    false false

------------------------------------------------------------------------
-- Existing WorldMonitor evidence-health owner remains authoritative for
-- freshness/genealogy/diversity/gap semantics.
------------------------------------------------------------------------

worldMonitorEvidenceHealthBoundary :
  Health.CounterUASWorldMonitorEvidenceHealthBoundary
worldMonitorEvidenceHealthBoundary =
  Health.canonicalCounterUASWorldMonitorEvidenceHealthBoundary

------------------------------------------------------------------------
-- Scorecard non-collapse boundary.
------------------------------------------------------------------------

record WorldMonitorForecastBoundary : Set where
  constructor world-monitor-forecast-boundary
  field
    headlineEqualsAllScoredPopulation : Bool
    headlineEqualsAllScoredPopulationIsFalse :
      headlineEqualsAllScoredPopulation ≡ false

    voidedEntriesBelongToAccuracyDenominator : Bool
    voidedEntriesBelongToAccuracyDenominatorIsFalse :
      voidedEntriesBelongToAccuracyDenominator ≡ false

    omittedCalibrationBucketMeansZeroRate : Bool
    omittedCalibrationBucketMeansZeroRateIsFalse :
      omittedCalibrationBucketMeansZeroRate ≡ false

    marketOverlapResultIsUniversalComparison : Bool
    marketOverlapResultIsUniversalComparisonIsFalse :
      marketOverlapResultIsUniversalComparison ≡ false

    unscoredHorizonsInheritHeadlineAccuracy : Bool
    unscoredHorizonsInheritHeadlineAccuracyIsFalse :
      unscoredHorizonsInheritHeadlineAccuracy ≡ false

canonicalWorldMonitorForecastBoundary : WorldMonitorForecastBoundary
canonicalWorldMonitorForecastBoundary =
  world-monitor-forecast-boundary
    false refl
    false refl
    false refl
    false refl
    false refl
