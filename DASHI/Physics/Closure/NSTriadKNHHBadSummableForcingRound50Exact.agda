module DASHI.Physics.Closure.NSTriadKNHHBadSummableForcingRound50Exact where

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
-- The strict-alpha recurrence is sufficient but need not be the only physical
-- doorway.  If the exact PDE gives the borderline normalized inheritance
--
--   C_(q+1) <= C_q + beta_q,
--
-- then a cutoff-independent ceiling still follows whenever the forcing has a
-- uniform finite prefix budget:
--
--   sum_{j<n} beta_j <= B    for every n.
--
-- We deliberately encode summability by bounded finite prefixes, which is the
-- exact property consumed by the shell induction and avoids importing an
-- unnecessary infinite-series representation into the rational closure layer.
-- The resulting theorem is
--
--   C_n <= C_0 + B,
--
-- and hence C_n<T for all n whenever C_0+B<T.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _≤_; _<_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

record BorderlineSummableForcing : Set where
  field
    profile forcing : Nat → ℚ
    forcingNonnegative : ∀ q → 0ℚ ≤ forcing q

    borderlineStep : ∀ q →
      profile (suc q) ≤ profile q + forcing q

    totalForcingBudget : ℚ
    totalForcingBudgetNonnegative : 0ℚ ≤ totalForcingBudget

open BorderlineSummableForcing public

forcingPrefix : BorderlineSummableForcing → Nat → ℚ
forcingPrefix input zero = 0ℚ
forcingPrefix input (suc n) =
  forcingPrefix input n + forcing input n

record PrefixSummable
    (input : BorderlineSummableForcing) : Set where
  field
    everyPrefixBelowBudget : ∀ n →
      forcingPrefix input n ≤ totalForcingBudget input

open PrefixSummable public

profileBelowBasePlusPrefix :
  (input : BorderlineSummableForcing) →
  ∀ n →
  profile input n
  ≤ profile input zero + forcingPrefix input n
profileBelowBasePlusPrefix input zero =
  subst
    (profile input zero ≤_)
    (solve (profile input zero ∷ []))
    ℚP.≤-refl
profileBelowBasePlusPrefix input (suc n) =
  let
    step :
      profile input (suc n)
      ≤ profile input n + forcing input n
    step = borderlineStep input n

    inherited :
      profile input n + forcing input n
      ≤ (profile input zero + forcingPrefix input n) + forcing input n
    inherited = ℚP.+-mono-≤
      (profileBelowBasePlusPrefix input n)
      ℚP.≤-refl

    combined :
      profile input (suc n)
      ≤ (profile input zero + forcingPrefix input n) + forcing input n
    combined = ℚP.≤-trans step inherited
  in
  subst
    (profile input (suc n) ≤_)
    (solve
      ( profile input zero
      ∷ forcingPrefix input n
      ∷ forcing input n
      ∷ []))
    combined

profileBelowBasePlusBudget :
  (input : BorderlineSummableForcing) →
  PrefixSummable input →
  ∀ n →
  profile input n
  ≤ profile input zero + totalForcingBudget input
profileBelowBasePlusBudget input summable n =
  ℚP.≤-trans
    (profileBelowBasePlusPrefix input n)
    (ℚP.+-mono-≤ ℚP.≤-refl (everyPrefixBelowBudget summable n))

record SummableForcingLiveTarget
    (input : BorderlineSummableForcing) : Set where
  field
    summable : PrefixSummable input
    target : ℚ
    basePlusBudgetStrict :
      profile input zero + totalForcingBudget input < target

open SummableForcingLiveTarget public

profileStrictlyBelowTarget :
  (input : BorderlineSummableForcing) →
  (live : SummableForcingLiveTarget input) →
  ∀ n → profile input n < target live
profileStrictlyBelowTarget input live n =
  ℚP.≤-<-trans
    (profileBelowBasePlusBudget input (summable live) n)
    (basePlusBudgetStrict live)

borderlineInheritanceWithSummableForcingClosesUniformProfile : Bool
borderlineInheritanceWithSummableForcingClosesUniformProfile = true

borderlineInheritanceWithSummableForcingClosesUniformProfileIsTrue :
  borderlineInheritanceWithSummableForcingClosesUniformProfile ≡ true
borderlineInheritanceWithSummableForcingClosesUniformProfileIsTrue = refl
