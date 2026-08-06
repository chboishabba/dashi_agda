module DASHI.Physics.Closure.NSTriadKNLuoSourceJ1J2CombinationExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and
-- Temporal Localization".
-- Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- PURPOSE
-- Formalize the literal time-window Cauchy step in equations (4.3)--(4.5):
--
--   J1 = sum_t h_t A_t B_t,
--   J11^2 = sum_t h_t A_t^2,
--   J12^2 = sum_t h_t B_t^2,
--
-- and derive J1^2 <= J11^2 J12^2 from the weighted Gram defect.  Separate
-- square budgets for J11, J12, and J2 are then transported to the complete
-- source nonlinear quantity.  Neither the product bound nor the final
-- recombination inequality is stored as a field.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; _+_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚₚ
open import Relation.Binary.PropositionalEquality using (subst; subst₂)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2
import DASHI.Physics.Closure.NSTriadKNLuoFiniteDyadicHalfSplitExact as SquareSum
import DASHI.Physics.Closure.NSTriadKNLuoFiniteWeightedCauchyExact as Cauchy

record FiniteSourceJ1Window (Time : Set) : Set where
  field
    times : List Time
    timeWeight leftFactor rightFactor : Time → ℚ
    timeWeightNonnegative :
      (time : Time) → 0ℚ ≤ timeWeight time

open FiniteSourceJ1Window public

weightedPairs :
  ∀ {Time} → FiniteSourceJ1Window Time → List Cauchy.WeightedPair
weightedPairs windowData = build (times windowData)
  where
  build : List Time → List Cauchy.WeightedPair
  build [] = []
  build (time ∷ remaining) =
    Cauchy.weighted-pair
      (timeWeight windowData time)
      (leftFactor windowData time)
      (rightFactor windowData time)
      (timeWeightNonnegative windowData time)
    ∷ build remaining

J1 : ∀ {Time} → FiniteSourceJ1Window Time → ℚ
J1 windowData = Cauchy.weightedPairing (weightedPairs windowData)

J11Squared : ∀ {Time} → FiniteSourceJ1Window Time → ℚ
J11Squared windowData = Cauchy.leftEnergy (weightedPairs windowData)

J12Squared : ∀ {Time} → FiniteSourceJ1Window Time → ℚ
J12Squared windowData = Cauchy.rightEnergy (weightedPairs windowData)

J1SquareBelowJ11J12 :
  ∀ {Time} (windowData : FiniteSourceJ1Window Time) →
  L2.square (J1 windowData)
  ≤ J11Squared windowData * J12Squared windowData
J1SquareBelowJ11J12 windowData =
  Cauchy.finiteWeightedCauchy (weightedPairs windowData)

weightedSquareEnergyNonnegative :
  (samples : List Cauchy.WeightedPair) →
  0ℚ ≤ Cauchy.leftEnergy samples
weightedSquareEnergyNonnegative [] = ℚₚ.≤-refl
weightedSquareEnergyNonnegative (sample ∷ samples) =
  L2.addNonnegative
    (let
      instance
        weightIsNonnegative =
          nonNegative (Cauchy.weightNonnegative sample)
        squareIsNonnegative =
          nonNegative (L2.squareNonnegative (Cauchy.left sample))
        productIsNonnegative =
          ℚₚ.nonNeg*nonNeg⇒nonNeg
            (Cauchy.weight sample)
            (L2.square (Cauchy.left sample))
     in
     ℚₚ.nonNegative⁻¹
       (Cauchy.weight sample * L2.square (Cauchy.left sample)))
    (weightedSquareEnergyNonnegative samples)

weightedRightSquareEnergyNonnegative :
  (samples : List Cauchy.WeightedPair) →
  0ℚ ≤ Cauchy.rightEnergy samples
weightedRightSquareEnergyNonnegative [] = ℚₚ.≤-refl
weightedRightSquareEnergyNonnegative (sample ∷ samples) =
  L2.addNonnegative
    (let
      instance
        weightIsNonnegative =
          nonNegative (Cauchy.weightNonnegative sample)
        squareIsNonnegative =
          nonNegative (L2.squareNonnegative (Cauchy.right sample))
        productIsNonnegative =
          ℚₚ.nonNeg*nonNeg⇒nonNeg
            (Cauchy.weight sample)
            (L2.square (Cauchy.right sample))
     in
     ℚₚ.nonNegative⁻¹
       (Cauchy.weight sample * L2.square (Cauchy.right sample)))
    (weightedRightSquareEnergyNonnegative samples)

record FiniteSourceJ1J2Budgets (Time : Set) : Set where
  field
    j1Window : FiniteSourceJ1Window Time
    j2 j11Budget j12Budget j2SquareBudget : ℚ

    j11BudgetNonnegative : 0ℚ ≤ j11Budget
    j12BudgetNonnegative : 0ℚ ≤ j12Budget
    j2SquareBudgetNonnegative : 0ℚ ≤ j2SquareBudget

    j11SquaredBound :
      J11Squared j1Window ≤ j11Budget
    j12SquaredBound :
      J12Squared j1Window ≤ j12Budget
    j2SquaredBound :
      L2.square j2 ≤ j2SquareBudget

open FiniteSourceJ1J2Budgets public

J1SquareBudget :
  ∀ {Time} (budgetData : FiniteSourceJ1J2Budgets Time) →
  L2.square (J1 (j1Window budgetData))
  ≤ j11Budget budgetData * j12Budget budgetData
J1SquareBudget budgetData =
  let
    window = j1Window budgetData
    samples = weightedPairs window

    first :
      J11Squared window * J12Squared window
      ≤ j11Budget budgetData * J12Squared window
    first =
      let
        instance
          rightEnergyIsNonnegative =
            nonNegative (weightedRightSquareEnergyNonnegative samples)
      in
      ℚₚ.*-monoʳ-≤-nonNeg
        (J12Squared window)
        (j11SquaredBound budgetData)

    second :
      j11Budget budgetData * J12Squared window
      ≤ j11Budget budgetData * j12Budget budgetData
    second =
      let
        instance
          leftBudgetIsNonnegative =
            nonNegative (j11BudgetNonnegative budgetData)
      in
      ℚₚ.*-monoˡ-≤-nonNeg
        (j11Budget budgetData)
        (j12SquaredBound budgetData)
  in
  ℚₚ.≤-trans
    (J1SquareBelowJ11J12 window)
    (ℚₚ.≤-trans first second)

sourceJ1J2SquareBudget :
  ∀ {Time} (budgetData : FiniteSourceJ1J2Budgets Time) →
  L2.square (J1 (j1Window budgetData) + j2 budgetData)
  ≤ SquareSum.two
      * ( j11Budget budgetData * j12Budget budgetData
        + j2SquareBudget budgetData)
sourceJ1J2SquareBudget budgetData =
  let
    algebra =
      SquareSum.squareOfSumBelowTwiceSquares
        (J1 (j1Window budgetData))
        (j2 budgetData)

    component :
      L2.square (J1 (j1Window budgetData))
        + L2.square (j2 budgetData)
      ≤ j11Budget budgetData * j12Budget budgetData
          + j2SquareBudget budgetData
    component =
      ℚₚ.+-mono-≤
        (J1SquareBudget budgetData)
        (j2SquaredBound budgetData)

    scaled :
      SquareSum.two
        * ( L2.square (J1 (j1Window budgetData))
          + L2.square (j2 budgetData))
      ≤ SquareSum.two
        * ( j11Budget budgetData * j12Budget budgetData
          + j2SquareBudget budgetData)
    scaled =
      let
        instance
          twoIsNonnegative =
            nonNegative SquareSum.twoNonnegative
      in
      ℚₚ.*-monoˡ-≤-nonNeg SquareSum.two component
  in
  ℚₚ.≤-trans algebra scaled
