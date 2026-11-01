module DASHI.Physics.Closure.NSTriadKNHHBadContractiveToWeightedGreenRound51Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale-Kato-Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- DOI: 10.1007/s00021-019-0411-z.
--
-- DASHI CONTRIBUTION
--
-- Complete the containment audit for the Round-51 master recurrence.  If the
-- variable coefficients are uniformly controlled by one alphaBar < 1 and the
-- forcing satisfies
--
--   beta_q <= (1-alphaBar) M,
--
-- then the weighted Green response itself stays <= M.  Hence the earlier
-- strict-contraction route is a direct special case of the weighted-Green
-- criterion, just as Round-50 raw summability is.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _≤_; _<_; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNHHBadWeightedGreenForcingRound51Exact as Green

record UniformContractiveGreenControl
    (input : Green.VariableGreenRecurrence) : Set where
  field
    alphaBar budget : ℚ
    alphaBarNonnegative : 0ℚ ≤ alphaBar
    alphaBarStrict : alphaBar < 1ℚ
    budgetNonnegative : 0ℚ ≤ budget
    alphaBelowBar : ∀ q → Green.alpha input q ≤ alphaBar
    forcingFitsBudget : ∀ q →
      Green.forcing input q ≤ (1ℚ - alphaBar) * budget

open UniformContractiveGreenControl public

greenStepPreservesUniformBudget :
  ∀ {input}
    (control : UniformContractiveGreenControl input) q →
  Green.weightedGreenResponse input q ≤ budget control →
  Green.weightedGreenResponse input (suc q) ≤ budget control
greenStepPreservesUniformBudget {input} control q current =
  let
    alphaTimesGreenBelowAlphaTimesBudget :
      Green.alpha input q * Green.weightedGreenResponse input q
      ≤ Green.alpha input q * budget control
    alphaTimesGreenBelowAlphaTimesBudget =
      let instance alphaNNI = nonNegative (Green.alphaNonnegative input q)
      in ℚP.*-monoˡ-≤-nonNeg (Green.alpha input q) current

    alphaTimesBudgetBelowBarTimesBudget :
      Green.alpha input q * budget control
      ≤ alphaBar control * budget control
    alphaTimesBudgetBelowBarTimesBudget =
      let instance budgetNNI = nonNegative (budgetNonnegative control)
      in ℚP.*-monoʳ-≤-nonNeg
        (budget control)
        (alphaBelowBar control q)

    first :
      Green.alpha input q * Green.weightedGreenResponse input q
        + Green.forcing input q
      ≤ alphaBar control * budget control + Green.forcing input q
    first =
      ℚP.+-mono-≤
        (ℚP.≤-trans
          alphaTimesGreenBelowAlphaTimesBudget
          alphaTimesBudgetBelowBarTimesBudget)
        ℚP.≤-refl

    second :
      alphaBar control * budget control + Green.forcing input q
      ≤ alphaBar control * budget control
        + (1ℚ - alphaBar control) * budget control
    second =
      ℚP.+-mono-≤
        ℚP.≤-refl
        (forcingFitsBudget control q)
  in
  ℚP.≤-trans first
    (ℚP.≤-trans second
      (subst
        (λ right →
          alphaBar control * budget control
            + (1ℚ - alphaBar control) * budget control ≤ right)
        (solve (alphaBar control ∷ budget control ∷ []))
        ℚP.≤-refl))

weightedGreenBelowContractiveBudget :
  ∀ {input}
    (control : UniformContractiveGreenControl input) →
  ∀ n → Green.weightedGreenResponse input n ≤ budget control
weightedGreenBelowContractiveBudget control zero =
  budgetNonnegative control
weightedGreenBelowContractiveBudget control (suc n) =
  greenStepPreservesUniformBudget control n
    (weightedGreenBelowContractiveBudget control n)

contractiveControlToWeightedBound :
  ∀ {input} →
  UniformContractiveGreenControl input →
  Green.UniformWeightedGreenBound input
contractiveControlToWeightedBound control = record
  { weightedBudget = budget control
  ; weightedBudgetNonnegative = budgetNonnegative control
  ; everyGreenResponseBelowBudget =
      weightedGreenBelowContractiveBudget control
  }

strictContractionIsContainedInWeightedGreenRoute : Bool
strictContractionIsContainedInWeightedGreenRoute = true

strictContractionIsContainedInWeightedGreenRouteIsTrue :
  strictContractionIsContainedInWeightedGreenRoute ≡ true
strictContractionIsContainedInWeightedGreenRouteIsTrue = refl
