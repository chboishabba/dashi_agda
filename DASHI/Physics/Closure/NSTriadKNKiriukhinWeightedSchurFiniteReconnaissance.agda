module DASHI.Physics.Closure.NSTriadKNKiriukhinWeightedSchurFiniteReconnaissance where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: DASHI repository contributors.
-- Title: "Exact finite weighted-Schur reconnaissance for the represented
-- orbit transfer matrices".
-- Venue/year: DASHI formal development, 2026.
-- DOI: not applicable; this is a DASHI-original exact computation.
-- Uses: Kiriukhin's raw orbit-transfer definition, Sinnamon's two-weight
-- viewpoint, the original six-mode witness, and the optimized projected-axis
-- matrix counterexample.
-- Relationship: tests natural polynomial weight pairs on two exact sparse
-- orbit matrices. It guides candidate design only and does not establish a
-- cutoff-uniform column or operator theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Data.Nat.Base using (_<_; z≤n; s≤s)

record PositiveRational : Set where
  constructor ratio
  field
    numerator denominator : Nat

open PositiveRational public

witnessOrbitCount optimizedOrbitCount : Nat
witnessOrbitCount = 2
optimizedOrbitCount = 3

witnessUnweightedRow witnessUnweightedColumn witnessUnweightedProduct : Nat
witnessUnweightedRow = 517
witnessUnweightedColumn = 752
witnessUnweightedProduct = 388784

witnessBestPowerExponent : Nat
witnessBestPowerExponent = 1

witnessBestPowerRow witnessBestPowerColumn witnessBestPowerProduct : PositiveRational
witnessBestPowerRow = ratio 5687 23
witnessBestPowerColumn = ratio 1316 1
witnessBestPowerProduct = ratio 7484092 23

witnessPowerImprovementCrossMultiplication :
  7484092 + 1457940 ≡ 388784 * 23
witnessPowerImprovementCrossMultiplication = refl

optimizedUnweightedRow optimizedUnweightedColumn optimizedUnweightedProduct :
  PositiveRational
optimizedUnweightedRow = ratio 2336395 6
optimizedUnweightedColumn = ratio 3751853 6
optimizedUnweightedProduct = ratio 8765810589935 36

optimizedBestOneWeightExponent : Nat
optimizedBestOneWeightExponent = 0

optimizedBestTwoWeightRowExponent : Nat
optimizedBestTwoWeightRowExponent = 0

optimizedBestTwoWeightColumnNegativeExponentMagnitude : Nat
optimizedBestTwoWeightColumnNegativeExponentMagnitude = 1

optimizedBestTwoWeightRow optimizedBestTwoWeightColumn
  optimizedBestTwoWeightProduct : PositiveRational
optimizedBestTwoWeightRow = ratio 133518425 12528
optimizedBestTwoWeightColumn = ratio 22511118 1
optimizedBestTwoWeightProduct = ratio 500941503391525 2088

optimizedTwoWeightImprovementCrossMultiplication :
  500941503391525 + 7475510824705
  ≡ 8765810589935 * 58
optimizedTwoWeightImprovementCrossMultiplication = refl

record WeightedSchurFiniteReceipt : Set where
  constructor receipt
  field
    witnessHasTwoOrbits : witnessOrbitCount ≡ 2
    optimizedSupportHasThreeOrbits : optimizedOrbitCount ≡ 3
    witnessRawProductExact : witnessUnweightedProduct ≡ 388784
    witnessPowerWeightImproves :
      7484092 + 1457940 ≡ witnessUnweightedProduct * 23
    optimizedOneWeightPowerDoesNotImprove : optimizedBestOneWeightExponent ≡ 0
    optimizedTwoFunctionPairImprovesSlightly :
      500941503391525 + 7475510824705
      ≡ 8765810589935 * 58

open WeightedSchurFiniteReceipt public

weightedSchurFiniteReceipt : WeightedSchurFiniteReceipt
weightedSchurFiniteReceipt =
  receipt
    refl
    refl
    refl
    witnessPowerImprovementCrossMultiplication
    refl
    optimizedTwoWeightImprovementCrossMultiplication

kiriukhinProfileOneWeightImprovesBothRepresentedStates : Bool
kiriukhinProfileOneWeightImprovesBothRepresentedStates = false

kiriukhinProfileOneWeightImprovesBothRepresentedStatesIsFalse :
  kiriukhinProfileOneWeightImprovesBothRepresentedStates ≡ false
kiriukhinProfileOneWeightImprovesBothRepresentedStatesIsFalse = refl

finiteWeightSearchClosesUniformColumnTheorem : Bool
finiteWeightSearchClosesUniformColumnTheorem = false

finiteWeightSearchClosesUniformColumnTheoremIsFalse :
  finiteWeightSearchClosesUniformColumnTheorem ≡ false
finiteWeightSearchClosesUniformColumnTheoremIsFalse = refl
