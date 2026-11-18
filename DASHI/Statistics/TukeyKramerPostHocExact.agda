module DASHI.Statistics.TukeyKramerPostHocExact where

-- Exact integer/rational comparison surface for TUKEY HSD / TUKEY-KRAMER.
--
-- This is intentionally distinct from Tukey IQR fences in Vec15Robust.
-- Requires the STUDENTIZED-RANGE quantile for declared (alpha,k,df),
-- externally supplied and calibrated (e.g. SciPy studentized_range.ppf).
-- The current finite arithmetic DOES NOT derive the distribution quantile.
--
-- Source: standard Tukey-Kramer unequal-n post-hoc formula
--   q^2 = (mean_i - mean_j)^2 / [ MSE/2 * (1/n_i + 1/n_j) ].
-- For sums s_i, s_j and sizes n_i, n_j, let
--   D = |s_i*n_j - s_j*n_i|.
-- q^2 = 2 D^2 MSEden / (MSEnum*n_i*n_j*(n_i+n_j)).
-- The rational studentized-range cutoff Qnum/Qden represents q_crit^2.
-- Compare integers:
-- 2 D^2 MSEden Qden > MSEnum n_i n_j(n_i+n_j) Qnum.
-- This is EXACT when group summaries/MSE are exact rational receipts
-- and Qnum/Qden is a declared rational threshold; approximating a true
-- irrational qcrit must be done with a conservative certified interval.
-- Exact comparison to an *uncertified* rounded threshold is NOT by itself
-- a family-wise-error guarantee.
--
-- Assumptions: independent groups, approximately normal residuals, common
-- variance, independent error, predeclared family of k means and positive
-- pooled residual df. Non-independent repeated-measure/clustered Bem data
-- require a different design (hierarchical mixed models or resampling).
-- This module is a reusable mathematical calculation, NOT a statistical
-- analysis of Bem's original workbooks.

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import DASHI.Core.Prelude using (⊥)

leq : Nat → Nat → Bool
leq zero _ = true
leq (suc _) zero = false
leq (suc n) (suc m) = leq n m

andBool : Bool → Bool → Bool
andBool true b = b
andBool false _ = false

notBool : Bool → Bool
notBool true = false
notBool false = true

lt : Nat → Nat → Bool
lt a b = notBool (leq b a)

minus : Nat → Nat → Nat
minus zero _ = zero
minus n zero = n
minus (suc n) (suc m) = minus n m

absoluteDifference : Nat → Nat → Nat
absoluteDifference a b with leq a b
... | true = minus b a
... | false = minus a b

square : Nat → Nat
square n = n * n

record GroupSummary : Set where
  constructor group-summary
  field
    count : Nat
    sum : Nat
open GroupSummary public

record PooledWithinVariance : Set where
  constructor pooled-variance
  field
    numerator : Nat
    denominator : Nat
    residualDegreesFreedom : Nat
open PooledWithinVariance public

record CalibratedRangeThreshold : Set where
  constructor range-threshold
  field
    qSquaredNumerator : Nat
    qSquaredDenominator : Nat
    familyCount : Nat
    confidenceReference : String
    alphaReference : String
    studentizedRangeCalibration : String
    independentlyCheckedCalibration : Bool
open CalibratedRangeThreshold public

record ExperimentAssumptions : Set where
  constructor assumptions
  field
    independentExperimentalUnits : Bool
    commonResidualVariance : Bool
    normalResidualApproximation : Bool
    predeclaredMeanFamily : Bool
    testedPostHocFamilyIsCorrect : Bool
open ExperimentAssumptions public

record PostHocDesign : Set where
  constructor posthoc-design
  field
    pooled : PooledWithinVariance
    threshold : CalibratedRangeThreshold
    assumptionsReceipt : ExperimentAssumptions
open PostHocDesign public

validGroup : GroupSummary → Bool
validGroup g = lt zero (count g)

validPooled : PooledWithinVariance → Bool
validPooled p =
  andBool (lt zero (numerator p))
  (andBool (lt zero (denominator p))
           (lt zero (residualDegreesFreedom p)))

validThreshold : CalibratedRangeThreshold → Bool
validThreshold t =
  andBool (lt zero (qSquaredDenominator t))
  (andBool (lt zero (familyCount t))
           (independentlyCheckedCalibration t))

validAssumptions : ExperimentAssumptions → Bool
validAssumptions a =
  andBool (independentExperimentalUnits a)
  (andBool (commonResidualVariance a)
  (andBool (normalResidualApproximation a)
  (andBool (predeclaredMeanFamily a)
           (testedPostHocFamilyIsCorrect a))))

admitted : PostHocDesign → GroupSummary → GroupSummary → Bool
admitted d a b =
  andBool (validGroup a)
  (andBool (validGroup b)
  (andBool (validPooled (pooled d))
  (andBool (validThreshold (threshold d))
           (validAssumptions (assumptionsReceipt d)))))

crossDifference : GroupSummary → GroupSummary → Nat
crossDifference a b =
  absoluteDifference (sum a * count b) (sum b * count a)

-- Positive MSE numerator and denominators are enforced by admitted.
statisticNumerator : PostHocDesign → GroupSummary → GroupSummary → Nat
statisticNumerator d a b =
  2 * square (crossDifference a b) * denominator (pooled d)

statisticDenominator : PostHocDesign → GroupSummary → GroupSummary → Nat
statisticDenominator d a b =
  numerator (pooled d) *
  count a * count b * (count a + count b)

data InferenceDisposition : Set where
  comparisonNotAdmitted : InferenceDisposition
  familyAdjustedReject : InferenceDisposition
  familyAdjustedFailToReject : InferenceDisposition

decide : PostHocDesign → GroupSummary → GroupSummary → InferenceDisposition
decide d a b with admitted d a b
... | false = comparisonNotAdmitted
... | true with lt
  (statisticDenominator d a b * qSquaredNumerator (threshold d))
  (statisticNumerator d a b * qSquaredDenominator (threshold d))
... | true | true = familyAdjustedReject
... | true | false = familyAdjustedFailToReject

-- FINITE SYNTHETIC arithmetic fixtures, not real Bem participants.
-- Three equal-n groups with pooled MSE=10, df=27, groups=3,
-- external 95% qcrit^2 about 12.295 (registered for illustration as
-- 12295/1000; this ROUNDED cutoff isn't a certified enclosure).
-- Pair means 10 vs 16: q^2=36 > 12.295; 10 vs 11: q^2=1.
syntheticAssumptions : ExperimentAssumptions
syntheticAssumptions = assumptions true true true true true

syntheticCutoff : CalibratedRangeThreshold
syntheticCutoff = range-threshold
  12295 1000 3
  "synthetic 0.95 studentized-range quantile"
  "alpha=.05"
  "studentized_range.ppf(.95, 3, 27) approx 3.506426"
  true

syntheticDesign : PostHocDesign
syntheticDesign = posthoc-design
  (pooled-variance 10 1 27)
  syntheticCutoff
  syntheticAssumptions

groupMean10 : GroupSummary
groupMean10 = group-summary 10 100

groupMean16 : GroupSummary
groupMean16 = group-summary 10 160

groupMean11 : GroupSummary
groupMean11 = group-summary 10 110

syntheticHighContrastReject :
  decide syntheticDesign groupMean10 groupMean16 ≡ familyAdjustedReject
syntheticHighContrastReject = refl

syntheticLowContrastFail :
  decide syntheticDesign groupMean10 groupMean11 ≡ familyAdjustedFailToReject
syntheticLowContrastFail = refl

syntheticInadmissibleAssumptions : ExperimentAssumptions
syntheticInadmissibleAssumptions =
  assumptions false true true true true

syntheticInvalidDesign : PostHocDesign
syntheticInvalidDesign = posthoc-design
  (pooled-variance 10 1 27)
  syntheticCutoff
  syntheticInadmissibleAssumptions

refusesNonIndependentExperimentalUnits :
  decide syntheticInvalidDesign groupMean10 groupMean16 ≡ comparisonNotAdmitted
refusesNonIndependentExperimentalUnits = refl

uncalibratedCutoff : CalibratedRangeThreshold
uncalibratedCutoff = range-threshold
  12295 1000 3
  "uncalibrated threshold" "alpha unknown" "no source" false

uncalibratedDesign : PostHocDesign
uncalibratedDesign = posthoc-design
  (pooled-variance 10 1 27)
  uncalibratedCutoff
  syntheticAssumptions

refusesUncalibratedThreshold :
  decide uncalibratedDesign groupMean10 groupMean16 ≡ comparisonNotAdmitted
refusesUncalibratedThreshold = refl

-- No theorem can infer that a user-written Boolean "assumptions true"
-- corresponds to a physical experiment. Provenance must be external.
data BooleanAssumptionLabelsProvePhysicalIndependence : Set where
data RoundedQuantileIsCertifiedExactFamilywiseAlpha : Set where
data TukeyPostHocIsBemPreregisteredPrimaryTest : Set where

noAssumptionBooleanAsPhysicalCertificate :
  BooleanAssumptionLabelsProvePhysicalIndependence → ⊥
noAssumptionBooleanAsPhysicalCertificate ()
noRoundedQuantileAsExactDistribution :
  RoundedQuantileIsCertifiedExactFamilywiseAlpha → ⊥
noRoundedQuantileAsExactDistribution ()
noTukeyAsOriginalBemTest :
  TukeyPostHocIsBemPreregisteredPrimaryTest → ⊥
noTukeyAsOriginalBemTest ()
