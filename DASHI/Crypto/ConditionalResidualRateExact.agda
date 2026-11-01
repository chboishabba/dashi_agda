module DASHI.Crypto.ConditionalResidualRateExact where

------------------------------------------------------------------------
-- FINITE CONDITIONAL / EXPECTED RESIDUAL RATE
--
-- A fibre-local residual need not pay its worst-case width on every coarse
-- observation.  This module keeps an exact weighted bit-mass numerator and total
-- weight denominator, avoiding floating probability or Shannon claims.  It is
-- the finite precursor to E[L(delta)|Y] and conditional information measures.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Data.Product using (_×_; _,_)

record WeightedResidualClass : Set where
  constructor weightedResidualClass
  field
    weight : Nat
    residualBits : Nat

open WeightedResidualClass public

weightSum : List WeightedResidualClass → Nat
weightSum [] = 0
weightSum (x ∷ xs) = weight x + weightSum xs

weightedBitMass : List WeightedResidualClass → Nat
weightedBitMass [] = 0
weightedBitMass (x ∷ xs) =
  weight x * residualBits x + weightedBitMass xs

record FiniteExpectedRate : Set where
  constructor finiteExpectedRate
  field
    numerator denominator : Nat

open FiniteExpectedRate public

expectedRate : List WeightedResidualClass → FiniteExpectedRate
expectedRate classes =
  finiteExpectedRate (weightedBitMass classes) (weightSum classes)

------------------------------------------------------------------------
-- Regression: ambiguous fibre occurs with weight 1 and needs one residual bit;
-- identified fibre occurs with weight 3 and needs zero bits.  Adaptive storage
-- therefore has bit-mass 1/4 rather than fixed one-bit storage 4/4.
------------------------------------------------------------------------

adaptiveClasses : List WeightedResidualClass
adaptiveClasses =
  weightedResidualClass 1 1 ∷
  weightedResidualClass 3 0 ∷ []

adaptiveExpectedRate : FiniteExpectedRate
adaptiveExpectedRate = expectedRate adaptiveClasses

adaptiveRateIsOneQuarter :
  numerator adaptiveExpectedRate ≡ 1
  × denominator adaptiveExpectedRate ≡ 4
adaptiveRateIsOneQuarter = refl , refl

fixedWidthClasses : List WeightedResidualClass
fixedWidthClasses =
  weightedResidualClass 1 1 ∷
  weightedResidualClass 3 1 ∷ []

fixedExpectedRate : FiniteExpectedRate
fixedExpectedRate = expectedRate fixedWidthClasses

fixedRateIsFourQuarters :
  numerator fixedExpectedRate ≡ 4
  × denominator fixedExpectedRate ≡ 4
fixedRateIsFourQuarters = refl , refl

adaptiveSavesThreeBitMassUnits :
  numerator fixedExpectedRate ≡ numerator adaptiveExpectedRate + 3
adaptiveSavesThreeBitMassUnits = refl

------------------------------------------------------------------------
-- Boundary: expected description rate, guessing probability, and computational
-- recovery cost remain separate coordinates.
------------------------------------------------------------------------

data ConditionalRateBoundary : Set where
  finiteRateIsNotSearchCost : ConditionalRateBoundary

conditionalRateBoundary : ConditionalRateBoundary
conditionalRateBoundary = finiteRateIsNotSearchCost
