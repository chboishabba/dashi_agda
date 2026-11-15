{-# OPTIONS --safe #-}
module DASHI.Quantum.QuantumBirthmarkNormalizedFiniteHistoryWeightExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; 1ℚ; _/_; _+_)
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Physics.Foundations.FiniteHistoryFunctionalExact as History
import DASHI.Quantum.QuantumBirthmarkCommonHistoryIdentityBenchmarkExact as Birthmark

biasedWeight : Birthmark.BirthmarkClass → History.History3 → ℚ
biasedWeight Birthmark.lowBirthmark
  (History.configurationA , (History.configurationB , History.configurationC)) = Int.+ 3 / 4
biasedWeight Birthmark.lowBirthmark
  (History.configurationA , (History.configurationC , History.configurationB)) = Int.+ 1 / 4
biasedWeight Birthmark.highBirthmark
  (History.configurationA , (History.configurationB , History.configurationC)) = Int.+ 1 / 4
biasedWeight Birthmark.highBirthmark
  (History.configurationA , (History.configurationC , History.configurationB)) = Int.+ 3 / 4
biasedWeight birthmark history = Int.+ 0 / 1

symmetricWeight : Birthmark.BirthmarkClass → History.History3 → ℚ
symmetricWeight birthmark
  (History.configurationA , (History.configurationB , History.configurationC)) = Int.+ 1 / 2
symmetricWeight birthmark
  (History.configurationA , (History.configurationC , History.configurationB)) = Int.+ 1 / 2
symmetricWeight birthmark history = Int.+ 0 / 1

lowBirthmarkWeightsNormalize :
  biasedWeight Birthmark.lowBirthmark History.historyABC
  + biasedWeight Birthmark.lowBirthmark History.historyACB
  ≡ 1ℚ
lowBirthmarkWeightsNormalize = solve []

highBirthmarkWeightsNormalize :
  biasedWeight Birthmark.highBirthmark History.historyABC
  + biasedWeight Birthmark.highBirthmark History.historyACB
  ≡ 1ℚ
highBirthmarkWeightsNormalize = solve []

symmetricWeightsNormalize :
  symmetricWeight Birthmark.lowBirthmark History.historyABC
  + symmetricWeight Birthmark.lowBirthmark History.historyACB
  ≡ 1ℚ
symmetricWeightsNormalize = solve []

biasedLowSelectsABCAtThreeQuarters :
  biasedWeight Birthmark.lowBirthmark History.historyABC ≡ Int.+ 3 / 4
biasedLowSelectsABCAtThreeQuarters = refl

symmetricLowWeightsABCAtHalf :
  symmetricWeight Birthmark.lowBirthmark History.historyABC ≡ Int.+ 1 / 2
symmetricLowWeightsABCAtHalf = refl

normalizedWeightLawNotUnique : Bool
normalizedWeightLawNotUnique = true

normalizedFiniteWeightModelOwned : Bool
normalizedFiniteWeightModelOwned = true

uniqueQuantumBornRuleDerived : Bool
uniqueQuantumBornRuleDerived = false

prxBirthmarkStatisticsSelectBiasedThreeQuarterLaw : Bool
prxBirthmarkStatisticsSelectBiasedThreeQuarterLaw = false

continuumNormalizedWeightLawStillRequired : Bool
continuumNormalizedWeightLawStillRequired = true
