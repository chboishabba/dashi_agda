module DASHI.Statistics.ForecastVerificationKernelExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; ½; _+_; _-_; _*_; _≤_)
open import Data.Rational.Tactic.RingSolver using (solve-∀)

------------------------------------------------------------------------
-- EXACT FINITE BINARY FORECAST VERIFICATION KERNEL
--
-- This module is intentionally small.  It does not recreate DASHI's existing
-- statistical-evidence, experiment-design, proof-search, provenance, or
-- consumer-authority machinery.  It supplies the missing exact operational
-- carrier on which those owners can act:
--
--   probability -> binary resolution -> proper-loss coordinate.
--
-- Analytic logarithms, sampling uncertainty, causal interpretation, and
-- decision authority remain separate receipts.
------------------------------------------------------------------------

data BinaryOutcome : Set where
  no yes : BinaryOutcome

record Probability : Set where
  constructor probability
  field
    value : ℚ
    lower : 0ℚ ≤ value
    upper : value ≤ 1ℚ

open Probability public

outcomeValue : BinaryOutcome → ℚ
outcomeValue no = 0ℚ
outcomeValue yes = 1ℚ

brierLossValue : ℚ → BinaryOutcome → ℚ
brierLossValue p outcome =
  let error = p - outcomeValue outcome
  in error * error

brierLoss : Probability → BinaryOutcome → ℚ
brierLoss p = brierLossValue (value p)

------------------------------------------------------------------------
-- Exact 1/2 baseline: either binary resolution gives loss 1/4.
------------------------------------------------------------------------

halfBaselineNo :
  brierLossValue ½ no ≡ ½ * ½
halfBaselineNo = refl

halfBaselineYes :
  brierLossValue ½ yes ≡ ½ * ½
halfBaselineYes =
  solve-∀

halfBaseline :
  (outcome : BinaryOutcome) →
  brierLossValue ½ outcome ≡ ½ * ½
halfBaseline no = halfBaselineNo
halfBaseline yes = halfBaselineYes

------------------------------------------------------------------------
-- Log-score seam.
--
-- As in FiniteVariationalFreeEnergyExact, logarithmic/surprisal coordinates are
-- supplied by an explicit receipt.  This module never fabricates an analytic
-- logarithm merely to score a finite ledger.
------------------------------------------------------------------------

record BinaryLogScoreCoordinates (p : Probability) : Set where
  constructor binary-log-score-coordinates
  field
    negLogP : ℚ
    negLogOneMinusP : ℚ
    coordinateReference : String
    analyticLogReceiptReference : String

open BinaryLogScoreCoordinates public

logLoss :
  {p : Probability} →
  BinaryLogScoreCoordinates p →
  BinaryOutcome →
  ℚ
logLoss coordinates no = negLogOneMinusP coordinates
logLoss coordinates yes = negLogP coordinates

record ScoredForecast : Set where
  constructor scored-forecast
  field
    forecastReference : String
    propositionReference : String
    probability : Probability
    outcome : BinaryOutcome
    resolutionReference : String

open ScoredForecast public

scoredBrierLoss : ScoredForecast → ℚ
scoredBrierLoss forecast =
  brierLoss (probability forecast) (outcome forecast)

------------------------------------------------------------------------
-- Odds geometry without denominator side conditions.
--
-- A probability p is represented by the homogeneous odds pair (p,1-p).
-- Cross-multiplication then expresses odds ratios and update factors exactly,
-- including a clean boundary at p=0 or p=1.  A later positive-interior adapter
-- may quotient this pair to the usual scalar p/(1-p).
------------------------------------------------------------------------

record OddsPair : Set where
  constructor odds-pair
  field
    favourable : ℚ
    unfavourable : ℚ

open OddsPair public

oddsPair : Probability → OddsPair
oddsPair p = odds-pair (value p) (1ℚ - value p)

record OddsUpdateReceipt (prior posterior : Probability) : Set where
  constructor odds-update-receipt
  field
    likelihoodNumerator : ℚ
    likelihoodDenominator : ℚ

    crossMultipliedUpdate :
      favourable (oddsPair posterior)
        * unfavourable (oddsPair prior)
        * likelihoodDenominator
      ≡
      unfavourable (oddsPair posterior)
        * favourable (oddsPair prior)
        * likelihoodNumerator

    evidenceReference : String
    calibrationReference : String

open OddsUpdateReceipt public

record OddsComparisonReceipt (left right : Probability) : Set where
  constructor odds-comparison-receipt
  field
    ratioNumerator : ℚ
    ratioDenominator : ℚ

    crossMultipliedRatio :
      favourable (oddsPair left)
        * unfavourable (oddsPair right)
        * ratioDenominator
      ≡
      unfavourable (oddsPair left)
        * favourable (oddsPair right)
        * ratioNumerator

    comparisonReference : String

open OddsComparisonReceipt public

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record ForecastVerificationKernelBoundary : Set where
  constructor forecast-verification-kernel-boundary
  field
    probabilityIsWorldState : Bool
    probabilityIsWorldStateIsFalse : probabilityIsWorldState ≡ false

    scoreIsForecastTruth : Bool
    scoreIsForecastTruthIsFalse : scoreIsForecastTruth ≡ false

    logCoordinatesInventedInternally : Bool
    logCoordinatesInventedInternallyIsFalse :
      logCoordinatesInventedInternally ≡ false

    oddsUpdateRequiresEvidenceReceipt : Bool
    oddsUpdateRequiresEvidenceReceiptIsTrue :
      oddsUpdateRequiresEvidenceReceipt ≡ true

    referenceClassRateAutomaticallyCaseProbability : Bool
    referenceClassRateAutomaticallyCaseProbabilityIsFalse :
      referenceClassRateAutomaticallyCaseProbability ≡ false

canonicalForecastVerificationKernelBoundary :
  ForecastVerificationKernelBoundary
canonicalForecastVerificationKernelBoundary =
  forecast-verification-kernel-boundary
    false refl
    false refl
    false refl
    true refl
    false refl
