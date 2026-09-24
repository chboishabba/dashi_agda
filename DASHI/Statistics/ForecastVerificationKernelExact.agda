module DASHI.Statistics.ForecastVerificationKernelExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; ½; _+_; _-_; _*_; -_; _≤_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNLuoFiniteRationalOrderCore as Order

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
halfBaselineNo = ℚRing.solve-∀

halfBaselineYes :
  brierLossValue ½ yes ≡ ½ * ½
halfBaselineYes =
  ℚRing.solve-∀

halfBaseline :
  (outcome : BinaryOutcome) →
  brierLossValue ½ outcome ≡ ½ * ½
halfBaseline no = halfBaselineNo
halfBaseline yes = halfBaselineYes

------------------------------------------------------------------------
-- Exact Brier range.
------------------------------------------------------------------------

oneNonnegative : 0ℚ ≤ 1ℚ
oneNonnegative = ℚP.nonNegative⁻¹ 1ℚ

subtractNonnegativeBelow :
  (value loss : ℚ) →
  0ℚ ≤ loss →
  value - loss ≤ value
subtractNonnegativeBelow value loss lossNonnegative =
  subst
    (λ upper → value + (- loss) ≤ upper)
    (ℚRing.solve-∀ value)
    (ℚP.+-mono-≤
      ℚP.≤-refl
      (subst
        (λ upper → - loss ≤ upper)
        (ℚRing.solve [])
        (ℚP.neg-mono-≤ lossNonnegative)))

unitSquareBound :
  (x : ℚ) →
  0ℚ ≤ x →
  x ≤ 1ℚ →
  x * x ≤ 1ℚ
unitSquareBound x xNonnegative xBelowOne =
  subst
    (λ upper → x * x ≤ upper)
    ℚRing.solve-∀
    (Order.nonnegativeProductMonotone
      xNonnegative xNonnegative
      oneNonnegative oneNonnegative
      xBelowOne xBelowOne)

brierLossNonnegative :
  (p : Probability) →
  (outcome : BinaryOutcome) →
  0ℚ ≤ brierLoss p outcome
brierLossNonnegative p outcome =
  Order.squareNonnegative
    (value p - outcomeValue outcome)

brierLossAtMostOne :
  (p : Probability) →
  (outcome : BinaryOutcome) →
  brierLoss p outcome ≤ 1ℚ
brierLossAtMostOne p no =
  let
    raw : value p * value p ≤ 1ℚ
    raw = unitSquareBound (value p) (lower p) (upper p)

    normal :
      value p * value p ≡ brierLoss p no
    normal = ℚRing.solve-∀ (value p)
  in
  subst (λ left → left ≤ 1ℚ) normal raw

brierLossAtMostOne p yes =
  let
    complement = 1ℚ - value p

    complementNonnegative : 0ℚ ≤ complement
    complementNonnegative =
      ℚP.p≤q⇒0≤q-p (upper p)

    complementBelowOne : complement ≤ 1ℚ
    complementBelowOne =
      subtractNonnegativeBelow 1ℚ (value p) (lower p)

    raw : complement * complement ≤ 1ℚ
    raw =
      unitSquareBound
        complement
        complementNonnegative
        complementBelowOne

    normal :
      complement * complement ≡ brierLoss p yes
    normal = ℚRing.solve-∀ (value p)
  in
  subst (λ left → left ≤ 1ℚ) normal raw

record BrierRangeReceipt
    (p : Probability)
    (outcome : BinaryOutcome) : Set where
  constructor brier-range-receipt
  field
    nonnegative : 0ℚ ≤ brierLoss p outcome
    atMostOne : brierLoss p outcome ≤ 1ℚ

canonicalBrierRangeReceipt :
  (p : Probability) →
  (outcome : BinaryOutcome) →
  BrierRangeReceipt p outcome
canonicalBrierRangeReceipt p outcome =
  brier-range-receipt
    (brierLossNonnegative p outcome)
    (brierLossAtMostOne p outcome)

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
