module DASHI.Physics.Closure.NSTriadKNHHBadHeadroomRound53Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale-Kato-Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- DASHI CONTRIBUTION
--
-- Exact algebra behind the physical proof strategy.  Writing the shell
-- capacity as M_q = C_* - d_q, the supersolution requirement
--
--   alpha_q M_q + beta_q <= M_(q+1)
--
-- is equivalent to
--
--   beta_q + d_(q+1)
--     <= (1-alpha_q) C_* + alpha_q d_q.
--
-- This exposes transient alpha_q > 1 as headroom consumption rather than a
-- forbidden event.  The theorem is arithmetic only; the PDE lane must still
-- identify its literal Duhamel terms with alpha, beta and d.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 1ℚ; _+_; _-_; _*_; _≤_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; sym)

capacityFromHeadroom : ℚ → ℚ → ℚ
capacityFromHeadroom ceiling depletion = ceiling - depletion

headroomBudget : ℚ → ℚ → ℚ → ℚ → ℚ → Set
headroomBudget alpha beta ceiling depletionNow depletionNext =
  beta + depletionNext
  ≤ (1ℚ - alpha) * ceiling + alpha * depletionNow

capacitySupersolution : ℚ → ℚ → ℚ → ℚ → ℚ → Set
capacitySupersolution alpha beta ceiling depletionNow depletionNext =
  alpha * capacityFromHeadroom ceiling depletionNow + beta
  ≤ capacityFromHeadroom ceiling depletionNext

headroomBudgetImpliesCapacitySupersolution :
  ∀ alpha beta ceiling depletionNow depletionNext →
  headroomBudget alpha beta ceiling depletionNow depletionNext →
  capacitySupersolution alpha beta ceiling depletionNow depletionNext
headroomBudgetImpliesCapacitySupersolution
    alpha beta ceiling depletionNow depletionNext budget =
  let
    lhsEquality :
      alpha * capacityFromHeadroom ceiling depletionNow + beta
      ≡ beta + alpha * ceiling - alpha * depletionNow
    lhsEquality = solve (alpha ∷ beta ∷ ceiling ∷ depletionNow ∷ [])

    rhsShifted :
      beta + alpha * ceiling - alpha * depletionNow
      ≤ ceiling - depletionNext
    rhsShifted =
      let
        shifted =
          Data.Rational.Properties.+-monoʳ-≤
            (alpha * ceiling - alpha * depletionNow - depletionNext)
            budget
      in
      subst
        (λ left → left ≤ ceiling - depletionNext)
        (solve
          ( beta ∷ depletionNext ∷ alpha ∷ ceiling
          ∷ depletionNow ∷ []))
        (subst
          (λ right →
            beta + depletionNext
              + (alpha * ceiling - alpha * depletionNow - depletionNext)
            ≤ right)
          (solve
            ( alpha ∷ beta ∷ ceiling ∷ depletionNow
            ∷ depletionNext ∷ []))
          shifted)
  in
  subst
    (λ left → left ≤ capacityFromHeadroom ceiling depletionNext)
    lhsEquality
    rhsShifted

capacitySupersolutionImpliesHeadroomBudget :
  ∀ alpha beta ceiling depletionNow depletionNext →
  capacitySupersolution alpha beta ceiling depletionNow depletionNext →
  headroomBudget alpha beta ceiling depletionNow depletionNext
capacitySupersolutionImpliesHeadroomBudget
    alpha beta ceiling depletionNow depletionNext capacity =
  let
    shifted =
      Data.Rational.Properties.+-monoʳ-≤
        (depletionNext + alpha * depletionNow)
        capacity
  in
  subst
    (λ left →
      left ≤ (1ℚ - alpha) * ceiling + alpha * depletionNow)
    (sym (solve
      (alpha ∷ beta ∷ ceiling ∷ depletionNow ∷ depletionNext ∷ [])))
    (subst
      (λ right →
        alpha * capacityFromHeadroom ceiling depletionNow + beta
          + (depletionNext + alpha * depletionNow)
        ≤ right)
      (solve
        (alpha ∷ beta ∷ ceiling ∷ depletionNow ∷ depletionNext ∷ []))
      shifted)

headroomCriterionIsExact : Bool
headroomCriterionIsExact = true

headroomCriterionIsExactIsTrue : headroomCriterionIsExact ≡ true
headroomCriterionIsExactIsTrue = refl
