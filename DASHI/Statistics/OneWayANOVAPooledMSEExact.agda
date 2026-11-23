module DASHI.Statistics.OneWayANOVAPooledMSEExact where

-- Exact 3-group one-way ANOVA POOLED WITHIN-GROUP MSE producer.
-- This fills the actual statistical quantity consumed by Tukey-Kramer;
-- unlike Vec15Inference's named "anova15", it computes an exact
-- residual sum of squares from group sufficient statistics.
--
-- For each group with size n>0, sum S and sum of squares Q:
--     SSE_i = Q - S^2/n = (n*Q-S^2)/n.
-- Three-group MSE =
--     (SSE_1+SSE_2+SSE_3)/(n1+n2+n3-3).
-- Our implementation uses common denominator n1*n2*n3,
-- so ALL operations before the final studentized-range cutoff are
-- exact integer arithmetic. It does NOT infer normality,
-- homoscedasticity, randomisation, independence, or correct
-- unit-of-analysis from these aggregated numbers alone.
--
-- This is not the original Bem analysis: his repeated-trial/session
-- structure requires source-accurate participant-level analysis, not
-- blindly one-way ANOVA on pseudo-independent trials.

open import Agda.Builtin.Nat using (Nat; _+_; _*_; zero; suc)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Core.Prelude using (⊥)

import DASHI.Statistics.TukeyKramerPostHocExact as HSD

record SquaredGroupSummary : Set where
  constructor squared-group-summary
  field
    count : Nat
    sum : Nat
    sumSquares : Nat
    rawDataChecksummed : Bool
open SquaredGroupSummary public

asGroupSummary : SquaredGroupSummary → HSD.GroupSummary
asGroupSummary group =
  HSD.group-summary (count group) (sum group)

-- Each term is n*sum(x²) - [sum(x)]², which is >=0 for authentic
-- real observations; a negative result signals invalid source moments.
validMoment : SquaredGroupSummary → Bool
validMoment group =
  HSD.andBool (HSD.lt zero (count group))
  (HSD.andBool (rawDataChecksummed group)
    (HSD.leq
      (HSD.square (sum group))
      (count group * sumSquares group)))

withinNumerator : SquaredGroupSummary → Nat
withinNumerator group =
  HSD.minus
    (count group * sumSquares group)
    (HSD.square (sum group))

record ThreeGroupANOVA : Set where
  constructor three-group-anova
  field
    first : SquaredGroupSummary
    second : SquaredGroupSummary
    third : SquaredGroupSummary
open ThreeGroupANOVA public

residualDF : ThreeGroupANOVA → Nat
residualDF groups =
  HSD.minus
    (count (first groups) + count (second groups) + count (third groups))
    3

commonDenominator : ThreeGroupANOVA → Nat
commonDenominator groups =
  count (first groups) * count (second groups) * count (third groups)

totalWithinNumerator : ThreeGroupANOVA → Nat
totalWithinNumerator groups =
  withinNumerator (first groups) *
    count (second groups) * count (third groups)
  + withinNumerator (second groups) *
    count (first groups) * count (third groups)
  + withinNumerator (third groups) *
    count (first groups) * count (second groups)

pooledMSE : ThreeGroupANOVA → HSD.PooledWithinVariance
pooledMSE groups =
  HSD.pooled-variance
    (totalWithinNumerator groups)
    (commonDenominator groups * residualDF groups)
    (residualDF groups)

validThreeGroupANOVA : ThreeGroupANOVA → Bool
validThreeGroupANOVA groups =
  HSD.andBool (validMoment (first groups))
  (HSD.andBool (validMoment (second groups))
  (HSD.andBool (validMoment (third groups))
    (HSD.lt zero (residualDF groups))))

-- These are SYNTHETIC group moments: each n=10, mean 10/16/11,
-- within-group SSE=90, residual df=27, pooled MSE=10.
syntheticThreeGroupANOVA : ThreeGroupANOVA
syntheticThreeGroupANOVA = three-group-anova
  (squared-group-summary 10 100 1090 true)
  (squared-group-summary 10 160 2650 true)
  (squared-group-summary 10 110 1300 true)

validSyntheticMoments :
  validThreeGroupANOVA syntheticThreeGroupANOVA ≡ true
validSyntheticMoments = refl

syntheticResidualDF :
  residualDF syntheticThreeGroupANOVA ≡ 27
syntheticResidualDF = refl

syntheticPooledNumerator :
  HSD.numerator (pooledMSE syntheticThreeGroupANOVA) ≡ 270000
syntheticPooledNumerator = refl

syntheticPooledDenominator :
  HSD.denominator (pooledMSE syntheticThreeGroupANOVA) ≡ 27000
syntheticPooledDenominator = refl

syntheticMSEIsExactlyTen :
  HSD.numerator (pooledMSE syntheticThreeGroupANOVA) ≡
  10 * HSD.denominator (pooledMSE syntheticThreeGroupANOVA)
syntheticMSEIsExactlyTen = refl

data SubmittedSufficientStatsProveRandomisation : Set where
data ThreeGroupANOVAMayTreatRepeatedTrialsAsIndependentPeople : Set where

noStatsAsDesignProof :
  SubmittedSufficientStatsProveRandomisation → ⊥
noStatsAsDesignProof ()
noTrialPseudoreplication :
  ThreeGroupANOVAMayTreatRepeatedTrialsAsIndependentPeople → ⊥
noTrialPseudoreplication ()
