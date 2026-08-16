module DASHI.Physics.Closure.NSTriadKNCriticalOwnerLanguageUniformBoundNoGoRound63Exact where

------------------------------------------------------------------------
-- ROUND 63 / C1 OWNER-LANGUAGE NO-GO
--
-- The owner language carries `integralCritical : ℚ` as a free physical scalar.
-- Therefore no scale-independent C1 constant can be derived from that carrier
-- alone.  For every nonnegative candidate K, choose the unit target T=1 and
-- the explicit environment
--
--       X = K + 1.
--
-- Then X > K = K*T, so the candidate bound fails.
--
-- This theorem prevents a future proof from accidentally closing C1 by record
-- structure, owner bookkeeping, or final capacity.  A uniform bound on the
-- normalized Xi_n must use genuinely additional selected-solution/localized-
-- flux mathematics.
--
-- The countermodel is elementary ordered-field arithmetic and uses no external
-- mathematical authority.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Empty using (⊥)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_; _<_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Nullary.Negation.Core using (¬_)

import DASHI.Physics.Closure.NSTriadKNAdmissibleOwnerTaxLanguageRound28Exact as Owner

unitScaleCounterEnvironment : ℚ → Owner.TaxEnvironment
unitScaleCounterEnvironment K = Owner.tax-environment 0ℚ (K + 1ℚ)

unitScaleCounterCritical :
  ∀ K → Owner.integralCritical (unitScaleCounterEnvironment K) ≡ K + 1ℚ
unitScaleCounterCritical K = refl

candidateStrictlyBelowCounterCritical :
  ∀ K → K < Owner.integralCritical (unitScaleCounterEnvironment K)
candidateStrictlyBelowCounterCritical K =
  let
    zeroLessOne : 0ℚ < 1ℚ
    zeroLessOne = ℚP.positive⁻¹ 1ℚ
    shifted : K + 0ℚ < K + 1ℚ
    shifted = ℚP.+-monoˡ-< K zeroLessOne
    leftMeaning : K + 0ℚ ≡ K
    leftMeaning = solve (K ∷ [])
  in
  subst (λ left → left < K + 1ℚ) leftMeaning shifted
  where
  open import Relation.Binary.PropositionalEquality using (subst)

ownerLanguageRefutesCandidateUnitScaleBound :
  ∀ K →
  ¬ (Owner.integralCritical (unitScaleCounterEnvironment K) ≤ K * 1ℚ)
ownerLanguageRefutesCandidateUnitScaleBound K candidate =
  ℚP.<-irrefl K
    (ℚP.<-≤-trans
      (candidateStrictlyBelowCounterCritical K)
      (subst
        (Owner.integralCritical (unitScaleCounterEnvironment K) ≤_)
        (solve (K ∷ []))
        candidate))
  where
  open import Relation.Binary.PropositionalEquality using (subst)

round63C1CannotComeFromOwnerLanguageAlone : Bool
round63C1CannotComeFromOwnerLanguageAlone = true

round63C1CannotComeFromOwnerLanguageAloneIsTrue :
  round63C1CannotComeFromOwnerLanguageAlone ≡ true
round63C1CannotComeFromOwnerLanguageAloneIsTrue = refl
