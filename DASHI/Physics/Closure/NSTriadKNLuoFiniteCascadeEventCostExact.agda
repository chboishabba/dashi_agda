module DASHI.Physics.Closure.NSTriadKNLuoFiniteCascadeEventCostExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Terence Tao.
-- Title: "Finite Time Blowup for an Averaged Three-Dimensional
-- Navier--Stokes Equation".
-- Journal of the American Mathematical Society 29 (2016), 601--674.
-- DOI: 10.1090/jams/838.
--
-- PURPOSE
-- Steelman the finite-energy cone argument and identify its exact missing
-- physical lemma.  If every cascade generation costs at least epsilon, then
-- N generations cost at least N*epsilon.  Combining this with a global budget
-- gives
--
--   N * epsilon <= totalBudget.
--
-- Thus finite energy rules out arbitrarily many generations only after a
-- scale-uniform positive event cost is proved.  The Zeno module shows why a
-- geometrically vanishing cost evades this argument.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_; here; there)
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

sumCosts : List ℚ → ℚ
sumCosts [] = 0ℚ
sumCosts (cost ∷ costs) = cost + sumCosts costs

rationalCount : List ℚ → ℚ
rationalCount [] = 0ℚ
rationalCount (cost ∷ costs) = 1ℚ + rationalCount costs

uniformCostLowerBound :
  (epsilon : ℚ) →
  (costs : List ℚ) →
  ((cost : ℚ) → cost ∈ costs → epsilon ≤ cost) →
  rationalCount costs * epsilon ≤ sumCosts costs
uniformCostLowerBound epsilon [] pointwise = ℚₚ.≤-refl
uniformCostLowerBound epsilon (cost ∷ costs) pointwise =
  let
    headBound : epsilon ≤ cost
    headBound = pointwise cost (here refl)

    tailPointwise :
      (tailCost : ℚ) → tailCost ∈ costs → epsilon ≤ tailCost
    tailPointwise tailCost membership =
      pointwise tailCost (there membership)

    tailBound :
      rationalCount costs * epsilon ≤ sumCosts costs
    tailBound = uniformCostLowerBound epsilon costs tailPointwise

    combined :
      epsilon + rationalCount costs * epsilon
      ≤ cost + sumCosts costs
    combined = ℚₚ.+-mono-≤ headBound tailBound
  in
  subst
    (λ lower → lower ≤ sumCosts (cost ∷ costs))
    (solve (rationalCount costs ∷ epsilon ∷ []))
    combined

finiteCascadeCountPaidByBudget :
  (epsilon totalBudget : ℚ) →
  (costs : List ℚ) →
  ((cost : ℚ) → cost ∈ costs → epsilon ≤ cost) →
  sumCosts costs ≤ totalBudget →
  rationalCount costs * epsilon ≤ totalBudget
finiteCascadeCountPaidByBudget epsilon totalBudget costs pointwise totalBound =
  ℚₚ.≤-trans
    (uniformCostLowerBound epsilon costs pointwise)
    totalBound
