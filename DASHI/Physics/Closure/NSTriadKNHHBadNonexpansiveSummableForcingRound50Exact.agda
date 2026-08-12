module DASHI.Physics.Closure.NSTriadKNHHBadNonexpansiveSummableForcingRound50Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale-Kato-Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- DASHI CONTRIBUTION
--
-- The fallback does not actually require alpha_q=1.  If
--
--   0 <= alpha_q <= 1,
--   0 <= C_q,
--   C_(q+1) <= alpha_q C_q + beta_q,
--
-- then alpha_q C_q <= C_q, hence
--
--   C_(q+1) <= C_q + beta_q.
--
-- Therefore any bounded-prefix forcing budget gives the same uniform ceiling
-- even with shell-dependent nonexpansive inheritance.  This retains the fine
-- alpha_q information while avoiding an unnecessary uniform gap inf_q(1-alpha_q)>0.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP

import DASHI.Physics.Closure.NSTriadKNHHBadSummableForcingRound50Exact as Sum

record NonexpansiveVariableForcingProfile : Set where
  field
    profile alpha forcing : Nat → ℚ
    profileNonnegative : ∀ q → 0ℚ ≤ profile q
    alphaNonnegative : ∀ q → 0ℚ ≤ alpha q
    alphaAtMostOne : ∀ q → alpha q ≤ 1ℚ
    forcingNonnegative : ∀ q → 0ℚ ≤ forcing q

    recurrence : ∀ q →
      profile (suc q) ≤ alpha q * profile q + forcing q

    totalForcingBudget : ℚ
    totalForcingBudgetNonnegative : 0ℚ ≤ totalForcingBudget

open NonexpansiveVariableForcingProfile public

alphaTimesProfileBelowProfile :
  (input : NonexpansiveVariableForcingProfile) →
  ∀ q → alpha input q * profile input q ≤ profile input q
alphaTimesProfileBelowProfile input q =
  let
    instance profileNNI = nonNegative (profileNonnegative input q)
    scaled :
      alpha input q * profile input q
      ≤ 1ℚ * profile input q
    scaled = ℚP.*-monoʳ-≤-nonNeg
      (profile input q)
      (alphaAtMostOne input q)
  in
  ℚP.≤-trans scaled ℚP.≤-refl

asBorderlineSummableForcing :
  NonexpansiveVariableForcingProfile →
  Sum.BorderlineSummableForcing
asBorderlineSummableForcing input = record
  { profile = profile input
  ; forcing = forcing input
  ; forcingNonnegative = forcingNonnegative input
  ; borderlineStep = λ q →
      ℚP.≤-trans
        (recurrence input q)
        (ℚP.+-mono-≤
          (alphaTimesProfileBelowProfile input q)
          ℚP.≤-refl)
  ; totalForcingBudget = totalForcingBudget input
  ; totalForcingBudgetNonnegative = totalForcingBudgetNonnegative input
  }

nonexpansiveVariableInheritanceNeedsNoUniformGapWhenForcingIsSummable : Bool
nonexpansiveVariableInheritanceNeedsNoUniformGapWhenForcingIsSummable = true

nonexpansiveVariableInheritanceNeedsNoUniformGapWhenForcingIsSummableIsTrue :
  nonexpansiveVariableInheritanceNeedsNoUniformGapWhenForcingIsSummable ≡ true
nonexpansiveVariableInheritanceNeedsNoUniformGapWhenForcingIsSummableIsTrue = refl
