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
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

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
    shift = alpha * ceiling - alpha * depletionNow - depletionNext

    shifted :
      shift + (beta + depletionNext)
      ≤ shift + ((1ℚ - alpha) * ceiling + alpha * depletionNow)
    shifted = ℚP.+-monoʳ-≤ shift budget

    leftMeaning :
      shift + (beta + depletionNext)
      ≡ alpha * capacityFromHeadroom ceiling depletionNow + beta
    leftMeaning =
      solve (alpha ∷ beta ∷ ceiling ∷ depletionNow ∷ depletionNext ∷ [])

    rightMeaning :
      shift + ((1ℚ - alpha) * ceiling + alpha * depletionNow)
      ≡ capacityFromHeadroom ceiling depletionNext
    rightMeaning =
      solve (alpha ∷ ceiling ∷ depletionNow ∷ depletionNext ∷ [])
  in
  subst
    (λ left → left ≤ capacityFromHeadroom ceiling depletionNext)
    leftMeaning
    (subst
      (λ right →
        shift + (beta + depletionNext) ≤ right)
      rightMeaning
      shifted)

capacitySupersolutionImpliesHeadroomBudget :
  ∀ alpha beta ceiling depletionNow depletionNext →
  capacitySupersolution alpha beta ceiling depletionNow depletionNext →
  headroomBudget alpha beta ceiling depletionNow depletionNext
capacitySupersolutionImpliesHeadroomBudget
    alpha beta ceiling depletionNow depletionNext capacity =
  let
    shift = depletionNext - alpha * ceiling + alpha * depletionNow

    shifted :
      shift
        + (alpha * capacityFromHeadroom ceiling depletionNow + beta)
      ≤ shift + capacityFromHeadroom ceiling depletionNext
    shifted = ℚP.+-monoʳ-≤ shift capacity

    leftMeaning :
      shift
        + (alpha * capacityFromHeadroom ceiling depletionNow + beta)
      ≡ beta + depletionNext
    leftMeaning =
      solve (alpha ∷ beta ∷ ceiling ∷ depletionNow ∷ depletionNext ∷ [])

    rightMeaning :
      shift + capacityFromHeadroom ceiling depletionNext
      ≡ (1ℚ - alpha) * ceiling + alpha * depletionNow
    rightMeaning =
      solve (alpha ∷ ceiling ∷ depletionNow ∷ depletionNext ∷ [])
  in
  subst
    (λ left →
      left ≤ (1ℚ - alpha) * ceiling + alpha * depletionNow)
    leftMeaning
    (subst
      (λ right →
        shift
          + (alpha * capacityFromHeadroom ceiling depletionNow + beta)
        ≤ right)
      rightMeaning
      shifted)

headroomCriterionIsExact : Bool
headroomCriterionIsExact = true

transientAlphaAboveOneAllowedByCriterion : Bool
transientAlphaAboveOneAllowedByCriterion = true

headroomCriterionIsExactIsTrue : headroomCriterionIsExact ≡ true
headroomCriterionIsExactIsTrue = refl

transientAlphaAboveOneAllowedByCriterionIsTrue :
  transientAlphaAboveOneAllowedByCriterion ≡ true
transientAlphaAboveOneAllowedByCriterionIsTrue = refl
