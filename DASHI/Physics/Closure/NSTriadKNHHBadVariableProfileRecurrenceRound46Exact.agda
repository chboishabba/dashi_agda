module DASHI.Physics.Closure.NSTriadKNHHBadVariableProfileRecurrenceRound46Exact where

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
-- Round 45 proved a fixed-coefficient recurrence criterion for the normalized
-- HH-bad profile C_q.  The physical shell transfer need not have constant
-- coefficients, so Round 46 preserves the finer statement
--
--   C_(q+1) <= alpha_q C_q + beta_q.
--
-- A single uniform contraction majorant alphaBar < 1 and forcing envelope
--
--   alpha_q <= alphaBar,
--   beta_q <= (1-alphaBar) M
--
-- suffice to propagate C_q <= M.  No product formula is postulated and no
-- shell-dependent information is discarded before the final induction step.
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

record VariableContractiveProfileRecurrence : Set where
  field
    profile alpha beta : Nat → ℚ
    alphaBar ceiling : ℚ

    profileNonnegative : ∀ q → 0ℚ ≤ profile q
    alphaNonnegative : ∀ q → 0ℚ ≤ alpha q
    betaNonnegative : ∀ q → 0ℚ ≤ beta q
    ceilingNonnegative : 0ℚ ≤ ceiling

    alphaBarNonnegative : 0ℚ ≤ alphaBar
    alphaBarStrict : alphaBar < 1ℚ
    alphaBelowBar : ∀ q → alpha q ≤ alphaBar

    baseBelowCeiling : profile zero ≤ ceiling
    recurrence : ∀ q →
      profile (suc q) ≤ alpha q * profile q + beta q

    forcingFitsUniformCeiling : ∀ q →
      beta q ≤ (1ℚ - alphaBar) * ceiling

open VariableContractiveProfileRecurrence public

variableRecurrenceStepPreservesCeiling :
  (data : VariableContractiveProfileRecurrence) →
  ∀ q →
  profile data q ≤ ceiling data →
  profile data (suc q) ≤ ceiling data
variableRecurrenceStepPreservesCeiling data q currentBelow =
  let
    alphaTimesProfileBelowAlphaTimesCeiling :
      alpha data q * profile data q
      ≤ alpha data q * ceiling data
    alphaTimesProfileBelowAlphaTimesCeiling =
      let instance alphaNNI = nonNegative (alphaNonnegative data q)
      in ℚP.*-monoˡ-≤-nonNeg (alpha data q) currentBelow

    alphaTimesCeilingBelowBarTimesCeiling :
      alpha data q * ceiling data
      ≤ alphaBar data * ceiling data
    alphaTimesCeilingBelowBarTimesCeiling =
      let instance ceilingNNI = nonNegative (ceilingNonnegative data)
      in ℚP.*-monoʳ-≤-nonNeg (ceiling data) (alphaBelowBar data q)

    first :
      alpha data q * profile data q + beta data q
      ≤ alphaBar data * ceiling data + beta data q
    first =
      ℚP.+-mono-≤
        (ℚP.≤-trans
          alphaTimesProfileBelowAlphaTimesCeiling
          alphaTimesCeilingBelowBarTimesCeiling)
        ℚP.≤-refl

    second :
      alphaBar data * ceiling data + beta data q
      ≤ alphaBar data * ceiling data
        + (1ℚ - alphaBar data) * ceiling data
    second =
      ℚP.+-monoʳ-≤
        (alphaBar data * ceiling data)
        (forcingFitsUniformCeiling data q)

    collapse :
      alphaBar data * ceiling data
        + (1ℚ - alphaBar data) * ceiling data
      ≡ ceiling data
    collapse = solve (alphaBar data ∷ ceiling data ∷ [])
  in
  ℚP.≤-trans
    (recurrence data q)
    (ℚP.≤-trans first
      (ℚP.≤-trans second
        (subst
          (λ upper →
            alphaBar data * ceiling data
              + (1ℚ - alphaBar data) * ceiling data
            ≤ upper)
          collapse
          ℚP.≤-refl)))

variableContractiveRecurrenceUniformCeiling :
  (data : VariableContractiveProfileRecurrence) →
  ∀ q → profile data q ≤ ceiling data
variableContractiveRecurrenceUniformCeiling data zero =
  baseBelowCeiling data
variableContractiveRecurrenceUniformCeiling data (suc q) =
  variableRecurrenceStepPreservesCeiling data q
    (variableContractiveRecurrenceUniformCeiling data q)

hhBadVariableProfileRecurrenceCriterionClosed : Bool
hhBadVariableProfileRecurrenceCriterionClosed = true

hhBadVariableProfileRecurrenceCriterionClosedIsTrue :
  hhBadVariableProfileRecurrenceCriterionClosed ≡ true
hhBadVariableProfileRecurrenceCriterionClosedIsTrue = refl
