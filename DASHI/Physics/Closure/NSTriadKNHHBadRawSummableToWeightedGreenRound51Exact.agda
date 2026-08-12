module DASHI.Physics.Closure.NSTriadKNHHBadRawSummableToWeightedGreenRound51Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale-Kato-Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- DOI: 10.1007/s00021-019-0411-z.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- DASHI CONTRIBUTION
--
-- Prove, rather than merely state, that Round 50 raw summability is contained
-- in the Round 51 weighted-Green criterion.  Under 0 <= alpha_q <= 1,
--
--   G_(q+1) = alpha_q G_q + beta_q <= G_q + beta_q,
--
-- so the exact weighted Green response is bounded by the raw forcing prefix.
-- Any Round-50 prefix budget is therefore automatically a Round-51 weighted
-- budget with the SAME constant.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Base using (ℚ; 1ℚ; _+_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNHHBadSummableForcingRound50Exact as Sum
import DASHI.Physics.Closure.NSTriadKNHHBadWeightedGreenForcingRound51Exact as Green

record RawSummableGreenInput : Set where
  field
    greenInput : Green.VariableGreenRecurrence
    rawInput : Sum.BorderlineSummableForcing

    sameProfile : ∀ q →
      Sum.profile rawInput q ≡ Green.profile greenInput q
    sameForcing : ∀ q →
      Sum.forcing rawInput q ≡ Green.forcing greenInput q

    rawPrefixSummable : Sum.PrefixSummable rawInput

open RawSummableGreenInput public

weightedGreenBelowRawPrefix :
  (input : RawSummableGreenInput) →
  ∀ n →
  Green.weightedGreenResponse (greenInput input) n
  ≤ Sum.forcingPrefix (rawInput input) n
weightedGreenBelowRawPrefix input zero = ℚP.≤-refl
weightedGreenBelowRawPrefix input (suc n) =
  let
    green = greenInput input
    raw = rawInput input

    alphaTimesGreenBelowGreen :
      Green.alpha green n * Green.weightedGreenResponse green n
      ≤ Green.weightedGreenResponse green n
    alphaTimesGreenBelowGreen =
      let instance greenNNI =
        nonNegative (Green.weightedGreenResponseNonnegative green n)
          
          
      scaled :
        Green.alpha green n * Green.weightedGreenResponse green n
        ≤ 1ℚ * Green.weightedGreenResponse green n
      scaled = ℚP.*-monoʳ-≤-nonNeg
        (Green.weightedGreenResponse green n)
        (Green.alphaAtMostOne green n)
      in
      subst
        (Green.alpha green n * Green.weightedGreenResponse green n ≤_)
        (solve (Green.weightedGreenResponse green n ∷ []))
        scaled

    oneStep :
      Green.alpha green n * Green.weightedGreenResponse green n
        + Green.forcing green n
      ≤ Green.weightedGreenResponse green n + Green.forcing green n
    oneStep = ℚP.+-mono-≤ alphaTimesGreenBelowGreen ℚP.≤-refl

    inherited :
      Green.weightedGreenResponse green n + Green.forcing green n
      ≤ Sum.forcingPrefix raw n + Sum.forcing raw n
    inherited =
      ℚP.+-mono-≤
        (weightedGreenBelowRawPrefix input n)
        (subst
          (Green.forcing green n ≤_)
          (sameForcing input n)
          ℚP.≤-refl)
  in
  ℚP.≤-trans oneStep inherited

rawSummableToWeightedBound :
  (input : RawSummableGreenInput) →
  Green.UniformWeightedGreenBound (greenInput input)
rawSummableToWeightedBound input = record
  { weightedBudget = Sum.totalForcingBudget (rawInput input)
  ; weightedBudgetNonnegative =
      Sum.totalForcingBudgetNonnegative (rawInput input)
  ; everyGreenResponseBelowBudget = λ n →
      ℚP.≤-trans
        (weightedGreenBelowRawPrefix input n)
        (Sum.everyPrefixBelowBudget (rawPrefixSummable input) n)
  }

round50RawSummabilityIsContainedInRound51WeightedGreen : Bool
round50RawSummabilityIsContainedInRound51WeightedGreen = true

round50RawSummabilityIsContainedInRound51WeightedGreenIsTrue :
  round50RawSummabilityIsContainedInRound51WeightedGreen ≡ true
round50RawSummabilityIsContainedInRound51WeightedGreenIsTrue = refl
