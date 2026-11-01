module DASHI.Physics.Closure.NSTriadKNComNormalizedSelfOverlapNoGoRound65Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Augustin-Louis Cauchy; Hermann Amandus Schwarz.
-- Result/context: equality case of the normalized self inner product.
-- DOI: not applicable to the original nineteenth-century results.
--
-- Authors: Tosio Kato; Gustavo Ponce.
-- Title: "Commutator Estimates and the Euler and Navier-Stokes Equations".
-- DOI: 10.1002/cpa.3160410704.
--
-- ROUND 65 / B1-B3 SEMANTIC FALSIFIER
--
-- A normalized Gram *self-correlation* of a nonzero row is exactly one.
-- Therefore the historical same-shell target 17/64 CANNOT be an upper bound
-- for `|<L_q,L_q>|^2/(||L_q||^2 ||L_q||^2)`.
--
-- This matters because Round64's wording could be read as asking B3 to prove
-- the six-three constants directly for the ordinary normalized correlation of
-- the q/r commutator rows.  At q=r that interpretation is mathematically
-- impossible: 1 <= 17/64 is false.
--
-- Hence the 17/64 and 65/512 constants must bound the repository's *full
-- factorized pair product* (or an internal branch overlap after the required
-- outer contractions), not ordinary normalized row self-correlation.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 1ℚ; _≤_; _<_)
import Data.Rational.Properties as ℚP
open ℚP using (_<?_)
open import Relation.Binary.PropositionalEquality using (subst)
open import Relation.Nullary.Decidable.Core using (toWitness)
open import Relation.Nullary.Negation.Core using (¬_)

import DASHI.Physics.Closure.NSTriadKNComNormalizedFibreMassLeafRound58 as Targets

sameShellTargetStrictlyBelowOne : Targets.sameShellTarget < 1ℚ
sameShellTargetStrictlyBelowOne =
  toWitness {a? = Targets.sameShellTarget <? 1ℚ} _

oneNotBelowSameShellTarget : ¬ (1ℚ ≤ Targets.sameShellTarget)
oneNotBelowSameShellTarget oneBelow =
  ℚP.<-irrefl 1ℚ
    (ℚP.<-≤-trans sameShellTargetStrictlyBelowOne oneBelow)

unitSelfOverlapCannotMeetSameShellTarget :
  (overlap : Nat → Nat → ℚ) →
  (∀ q → overlap q q ≡ 1ℚ) →
  ¬ (∀ q → overlap q q ≤ Targets.sameShellTarget)
unitSelfOverlapCannotMeetSameShellTarget overlap selfIsOne allBound =
  oneNotBelowSameShellTarget
    (subst
      (λ value → value ≤ Targets.sameShellTarget)
      (selfIsOne 0)
      (allBound 0))

round65OrdinaryNormalizedSelfCorrelationIsNotSixThreeSameShellTarget : Bool
round65OrdinaryNormalizedSelfCorrelationIsNotSixThreeSameShellTarget = true

round65OrdinaryNormalizedSelfCorrelationIsNotSixThreeSameShellTargetIsTrue :
  round65OrdinaryNormalizedSelfCorrelationIsNotSixThreeSameShellTarget ≡ true
round65OrdinaryNormalizedSelfCorrelationIsNotSixThreeSameShellTargetIsTrue = refl
