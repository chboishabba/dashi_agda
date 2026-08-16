module DASHI.Physics.Closure.NSTriadKNCriticalScaleAbstractEnvironmentNoGoRound63Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- ROUND 63 C1 FALSIFIER
--
-- `TaxEnvironment.integralCritical` is an unconstrained rational at the owner
-- grammar layer.  Therefore no theorem at that abstraction level can produce
-- the missing uniform critical-scale estimate.  For ANY proposed K and block
-- target T, this file constructs an actual TaxEnvironment with
--
--   integralCritical = K*T + 1 > K*T.
--
-- Hence C1 must be proved only after a selected-solution/block constructor has
-- identified `integralCritical` with the literal physical block functional.
-- This is a counterexample to an invalid proof route, not a replacement for
-- that analytic theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_; _<_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNAdmissibleOwnerTaxLanguageRound28Exact as Owner

adversarialEnvironment : ℚ → ℚ → Owner.TaxEnvironment
adversarialEnvironment K target =
  Owner.tax-environment 0ℚ (K * target + 1ℚ)

adversarialCriticalExact :
  (K target : ℚ) →
  Owner.integralCritical (adversarialEnvironment K target)
  ≡ K * target + 1ℚ
adversarialCriticalExact K target = refl

adversarialCriticalStrictlyExceedsProposedScale :
  (K target : ℚ) →
  K * target
  < Owner.integralCritical (adversarialEnvironment K target)
adversarialCriticalStrictlyExceedsProposedScale K target =
  subst
    (λ right → K * target < right)
    (sym (adversarialCriticalExact K target))
    (ℚP.+-monoʳ-< (K * target) ℚP.0<1)
  where
  open import Relation.Binary.PropositionalEquality using (sym)

adversarialEnvironmentRefutesProposedBound :
  (K target : ℚ) →
  ¬ (Owner.integralCritical (adversarialEnvironment K target) ≤ K * target)
adversarialEnvironmentRefutesProposedBound K target proposed =
  ℚP.<-irrefl refl
    (ℚP.<-≤-trans
      (adversarialCriticalStrictlyExceedsProposedScale K target)
      proposed)
  where
  open import Relation.Nullary using (¬_)

ownerGrammarCannotProveC1 : Bool
ownerGrammarCannotProveC1 = true

c1RequiresSelectedPhysicalEnvironment : Bool
c1RequiresSelectedPhysicalEnvironment = true

ownerGrammarCannotProveC1IsTrue : ownerGrammarCannotProveC1 ≡ true
ownerGrammarCannotProveC1IsTrue = refl

c1RequiresSelectedPhysicalEnvironmentIsTrue :
  c1RequiresSelectedPhysicalEnvironment ≡ true
c1RequiresSelectedPhysicalEnvironmentIsTrue = refl
