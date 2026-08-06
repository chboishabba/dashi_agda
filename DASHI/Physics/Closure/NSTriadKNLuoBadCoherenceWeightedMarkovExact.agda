module DASHI.Physics.Closure.NSTriadKNLuoBadCoherenceWeightedMarkovExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Authors: Peter Constantin; Charles Fefferman.
-- Title: "Direction of Vorticity and the Problem of Global Regularity for
-- the Navier--Stokes Equations".
-- DOI: 10.1512/iumj.1993.42.42014.
--
-- Author: Zoran Grujić.
-- Title: "A Geometric Measure-Type Regularity Criterion for Solutions to the
-- 3D Navier-Stokes Equations".
-- DOI: 10.1088/0951-7715/26/1/289.
-- arXiv DOI: 10.48550/arXiv.1111.0217.
--
-- PURPOSE
-- Advance the bad-coherence frontier by proving the exact finite weighted
-- Markov bridge. On every bad cell the directional defect theta satisfies
--
--   delta <= theta.
--
-- Hence, for nonnegative interaction weights,
--
--   delta * badWeightMass <= weightedDefectMass.
--
-- If the weighted defect is further bounded by delta times a rarity envelope,
-- positivity of delta cancels it and yields
--
--   badWeightMass <= rarityEnvelope.
--
-- Therefore vanishing of the normalized weighted-defect envelope implies
-- vanishing bad mass. What remains genuinely new is proving that normalized
-- defect envelope tends to zero for the physical Navier--Stokes carrier.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_; _<_; nonNegative)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; cong; trans; sym)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2
import DASHI.Physics.Closure.NSTriadKNLuoFiniteEightPointSixThreeHolderExact as Holder
import DASHI.Physics.Closure.NSTriadKNLuoTerminalInteractionDepletionTransferExact as Limit

record PositiveThreshold : Set where
  constructor positive-threshold
  field
    threshold thresholdInverse : ℚ
    thresholdPositive : 0ℚ < threshold
    thresholdInverseNonnegative : 0ℚ ≤ thresholdInverse
    inverseMeaning : thresholdInverse * threshold ≡ 1ℚ

open PositiveThreshold public

thresholdNonnegative :
  (parameter : PositiveThreshold) →
  0ℚ ≤ threshold parameter
thresholdNonnegative parameter =
  ℚₚ.<⇒≤ (thresholdPositive parameter)

record BadCoherenceCell (parameter : PositiveThreshold) : Set where
  constructor bad-coherence-cell
  field
    weight defect : ℚ
    weightNonnegative : 0ℚ ≤ weight
    defectNonnegative : 0ℚ ≤ defect
    badThreshold : threshold parameter ≤ defect

open BadCoherenceCell public

badWeightMass :
  (parameter : PositiveThreshold) →
  List (BadCoherenceCell parameter) →
  ℚ
badWeightMass parameter [] = 0ℚ
badWeightMass parameter (cell ∷ cells) =
  weight cell + badWeightMass parameter cells

weightedDefectMass :
  (parameter : PositiveThreshold) →
  List (BadCoherenceCell parameter) →
  ℚ
weightedDefectMass parameter [] = 0ℚ
weightedDefectMass parameter (cell ∷ cells) =
  weight cell * defect cell + weightedDefectMass parameter cells

badWeightMassNonnegative :
  (parameter : PositiveThreshold) →
  (cells : List (BadCoherenceCell parameter)) →
  0ℚ ≤ badWeightMass parameter cells
badWeightMassNonnegative parameter [] = ℚₚ.≤-refl
badWeightMassNonnegative parameter (cell ∷ cells) =
  L2.addNonnegative
    (weightNonnegative cell)
    (badWeightMassNonnegative parameter cells)

weightedDefectMassNonnegative :
  (parameter : PositiveThreshold) →
  (cells : List (BadCoherenceCell parameter)) →
  0ℚ ≤ weightedDefectMass parameter cells
weightedDefectMassNonnegative parameter [] = ℚₚ.≤-refl
weightedDefectMassNonnegative parameter (cell ∷ cells) =
  let
    productNN : 0ℚ ≤ weight cell * defect cell
    productNN =
      let
        instance
          weightNNI = nonNegative (weightNonnegative cell)
          defectNNI = nonNegative (defectNonnegative cell)
          resultNN = ℚₚ.nonNeg*nonNeg⇒nonNeg (weight cell) (defect cell)
      in
      ℚₚ.nonNegative⁻¹ (weight cell * defect cell)
  in
  L2.addNonnegative
    productNN
    (weightedDefectMassNonnegative parameter cells)

thresholdTimesBadWeightBelowDefect :
  (parameter : PositiveThreshold) →
  (cells : List (BadCoherenceCell parameter)) →
  threshold parameter * badWeightMass parameter cells
  ≤ weightedDefectMass parameter cells
thresholdTimesBadWeightBelowDefect parameter [] = ℚₚ.≤-refl
thresholdTimesBadWeightBelowDefect parameter (cell ∷ cells) =
  let
    localUncommuted :
      threshold parameter * weight cell
      ≤ defect cell * weight cell
    localUncommuted =
      L2.nonnegativeProductMonotone
        (thresholdNonnegative parameter)
        (weightNonnegative cell)
        (defectNonnegative cell)
        (weightNonnegative cell)
        (badThreshold cell)
        ℚₚ.≤-refl

    local :
      threshold parameter * weight cell
      ≤ weight cell * defect cell
    local =
      subst
        (λ upper → threshold parameter * weight cell ≤ upper)
        (solve (weight cell ∷ defect cell ∷ []))
        localUncommuted

    tail = thresholdTimesBadWeightBelowDefect parameter cells
    summed = ℚₚ.+-mono-≤ local tail

    leftMeaning :
      threshold parameter
        * (weight cell + badWeightMass parameter cells)
      ≡ threshold parameter * weight cell
        + threshold parameter * badWeightMass parameter cells
    leftMeaning =
      solve
        ( threshold parameter
        ∷ weight cell
        ∷ badWeightMass parameter cells
        ∷ [])
  in
  subst
    (λ lower →
      lower
      ≤ weight cell * defect cell
        + weightedDefectMass parameter cells)
    (sym leftMeaning)
    summed

positiveThresholdCancellation :
  (parameter : PositiveThreshold) →
  (left right : ℚ) →
  threshold parameter * left ≤ threshold parameter * right →
  left ≤ right
positiveThresholdCancellation parameter left right scaledBound =
  let
    rescaled :
      thresholdInverse parameter * (threshold parameter * left)
      ≤ thresholdInverse parameter * (threshold parameter * right)
    rescaled =
      Holder.scaleBound
        (thresholdInverse parameter)
        (threshold parameter * left)
        (threshold parameter * right)
        (thresholdInverseNonnegative parameter)
        scaledBound

    leftFactorized :
      thresholdInverse parameter * (threshold parameter * left)
      ≡ (thresholdInverse parameter * threshold parameter) * left
    leftFactorized =
      solve
        (thresholdInverse parameter ∷ threshold parameter ∷ left ∷ [])

    rightFactorized :
      thresholdInverse parameter * (threshold parameter * right)
      ≡ (thresholdInverse parameter * threshold parameter) * right
    rightFactorized =
      solve
        (thresholdInverse parameter ∷ threshold parameter ∷ right ∷ [])

    leftReplace :
      (thresholdInverse parameter * threshold parameter) * left
      ≡ 1ℚ * left
    leftReplace =
      cong (λ factor → factor * left) (inverseMeaning parameter)

    rightReplace :
      (thresholdInverse parameter * threshold parameter) * right
      ≡ 1ℚ * right
    rightReplace =
      cong (λ factor → factor * right) (inverseMeaning parameter)

    leftNormalize : 1ℚ * left ≡ left
    leftNormalize = solve (left ∷ [])

    rightNormalize : 1ℚ * right ≡ right
    rightNormalize = solve (right ∷ [])

    leftMeaning = trans leftFactorized (trans leftReplace leftNormalize)
    rightMeaning = trans rightFactorized (trans rightReplace rightNormalize)
  in
  subst
    (λ lower → lower ≤ right)
    leftMeaning
    (subst
      (λ upper →
        thresholdInverse parameter * (threshold parameter * left)
        ≤ upper)
      rightMeaning
      rescaled)

record DynamicWeightedBadRarity : Set where
  constructor dynamic-weighted-bad-rarity
  field
    parameter : Nat → PositiveThreshold
    badMass rarityEnvelope : Nat → ℚ

    scaledBadByRarity :
      (shell : Nat) →
      threshold (parameter shell) * badMass shell
      ≤ threshold (parameter shell) * rarityEnvelope shell

open DynamicWeightedBadRarity public

badMassBelowRarityEnvelope :
  (dataSet : DynamicWeightedBadRarity) →
  (shell : Nat) →
  badMass dataSet shell ≤ rarityEnvelope dataSet shell
badMassBelowRarityEnvelope dataSet shell =
  positiveThresholdCancellation
    (parameter dataSet shell)
    (badMass dataSet shell)
    (rarityEnvelope dataSet shell)
    (scaledBadByRarity dataSet shell)

badMassVanishingFromNormalizedDefect :
  (dataSet : DynamicWeightedBadRarity) →
  Limit.TendsToZero (rarityEnvelope dataSet) →
  Limit.TendsToZero (badMass dataSet)
badMassVanishingFromNormalizedDefect dataSet rarityVanishing =
  Limit.interactionDepletionFromCriticalDepletion
    (Limit.critical-to-interaction-data
      (badMass dataSet)
      (rarityEnvelope dataSet)
      (badMassBelowRarityEnvelope dataSet))
    rarityVanishing
