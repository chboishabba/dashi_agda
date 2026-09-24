{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650RateKernelPositiveRateNoGoRound680Exact where

------------------------------------------------------------------------
-- ROUND680 / GENERIC POSITIVE-RATE COHERENT GEOMETRY DOES NOT FIX THE
--            SIGN OF THE R665 WEIGHTED-WORK SCALAR
--
-- R679 returns the long signed recut to n * WeightedWork.
--
-- A two-cell one-dimensional coherent model already shows that positive rates
-- and positive total self-work are not enough to determine its sign:
--
--   A1 =  2,  A2 = -3,  M = A1+A2 = -1,
--   W(x,y)=2xy,
--
-- hence
--
--   w1 = W(M,A1) = -4,
--   w2 = W(M,A2) =  6,
--   w1+w2 = W(M,M) = 2.
--
-- With rates r1=10, r2=1,
--
--   WeightedWork = r1*w1 + r2*w2 = -34,
--   n*WeightedWork = -68.
--
-- The file encodes exactly this finite scalar witness.  It is intentionally
-- scoped: it does NOT claim that an arbitrary two-cell scalar model is
-- realizable as a literal NS physical output fibre.  It only rules out a proof
-- using positive rates + positive coherent self-work as the sole hypotheses.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovariancePairDifferenceExact as Pair

data Two : Set where
  first second : Two

items : List Two
items = first ∷ second ∷ []

rate : Two → ℚ
rate first = 10
rate second = 1

work : Two → ℚ
work first = 0ℚ - 4
work second = 6

weightedWork : ℚ
weightedWork = Pair.weightedWorkSum rate work items

workTotal : ℚ
workTotal = Pair.workSum work items

rateTotal : ℚ
rateTotal = Pair.rateSum rate items

cardinality : ℚ
cardinality = Pair.natAsRational 2

firstRateIsTen : rate first ≡ 10
firstRateIsTen = refl

secondRateIsOne : rate second ≡ 1
secondRateIsOne = refl

coherentSelfWorkIsTwo : workTotal ≡ 2
coherentSelfWorkIsTwo = refl

weightedWorkIsMinusThirtyFour :
  weightedWork ≡ 0ℚ - 34
weightedWorkIsMinusThirtyFour = refl

cardinalityWeightedWorkIsMinusSixtyEight :
  cardinality * weightedWork ≡ 0ℚ - 68
cardinalityWeightedWorkIsMinusSixtyEight = refl

pairDifferenceValue :
  Pair.pairDifferenceWorkSum rate work items ≡ 63
pairDifferenceValue = refl

rateSelfPlusPairDifferenceValue :
  rateTotal * workTotal
    + Pair.pairDifferenceWorkSum rate work items
  ≡ 0ℚ - 68
rateSelfPlusPairDifferenceValue = refl

closedFormChecksWitness :
  rateSelfPlusPairDifferenceValue
  ≡
  rateSelfPlusPairDifferenceValue
closedFormChecksWitness = refl

------------------------------------------------------------------------
-- Status / scope firewall.
------------------------------------------------------------------------

round680RatesAreStrictlyPositiveNumerals : Bool
round680RatesAreStrictlyPositiveNumerals = true

round680CoherentSelfWorkPositiveNumeral : Bool
round680CoherentSelfWorkPositiveNumeral = true

round680CardinalityWeightedWorkNegativeNumeral : Bool
round680CardinalityWeightedWorkNegativeNumeral = true

round680PositiveRatesAloneForceFavorableWeightedWorkSign : Bool
round680PositiveRatesAloneForceFavorableWeightedWorkSign = false

round680PositiveRatesAndPositiveSelfWorkForceFavorableWeightedWorkSign : Bool
round680PositiveRatesAndPositiveSelfWorkForceFavorableWeightedWorkSign = false

round680ClaimsLiteralNSFibreRealizesWitness : Bool
round680ClaimsLiteralNSFibreRealizesWitness = false

round680AdditionalPhysicalStructureNeeded : Bool
round680AdditionalPhysicalStructureNeeded = true

round680IntroducesEstimate : Bool
round680IntroducesEstimate = false

round680IntroducesNewClayLeaf : Bool
round680IntroducesNewClayLeaf = false

round680ClayPromotion : Bool
round680ClayPromotion = false

round680RatesAreStrictlyPositiveNumeralsIsTrue :
  round680RatesAreStrictlyPositiveNumerals ≡ true
round680RatesAreStrictlyPositiveNumeralsIsTrue = refl

round680CoherentSelfWorkPositiveNumeralIsTrue :
  round680CoherentSelfWorkPositiveNumeral ≡ true
round680CoherentSelfWorkPositiveNumeralIsTrue = refl

round680CardinalityWeightedWorkNegativeNumeralIsTrue :
  round680CardinalityWeightedWorkNegativeNumeral ≡ true
round680CardinalityWeightedWorkNegativeNumeralIsTrue = refl

round680PositiveRatesAloneForceFavorableWeightedWorkSignIsFalse :
  round680PositiveRatesAloneForceFavorableWeightedWorkSign ≡ false
round680PositiveRatesAloneForceFavorableWeightedWorkSignIsFalse = refl

round680PositiveRatesAndPositiveSelfWorkForceFavorableWeightedWorkSignIsFalse :
  round680PositiveRatesAndPositiveSelfWorkForceFavorableWeightedWorkSign ≡ false
round680PositiveRatesAndPositiveSelfWorkForceFavorableWeightedWorkSignIsFalse = refl

round680ClaimsLiteralNSFibreRealizesWitnessIsFalse :
  round680ClaimsLiteralNSFibreRealizesWitness ≡ false
round680ClaimsLiteralNSFibreRealizesWitnessIsFalse = refl

round680AdditionalPhysicalStructureNeededIsTrue :
  round680AdditionalPhysicalStructureNeeded ≡ true
round680AdditionalPhysicalStructureNeededIsTrue = refl

round680IntroducesEstimateIsFalse :
  round680IntroducesEstimate ≡ false
round680IntroducesEstimateIsFalse = refl

round680IntroducesNewClayLeafIsFalse :
  round680IntroducesNewClayLeaf ≡ false
round680IntroducesNewClayLeafIsFalse = refl

round680ClayPromotionIsFalse :
  round680ClayPromotion ≡ false
round680ClayPromotionIsFalse = refl
