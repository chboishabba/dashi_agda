module DASHI.Physics.Closure.NSTriadKNCriticalAntichainBudgetNoGoRound75Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: P. A. P. Moran.
-- Title: "Additive functions of intervals and Hausdorff measure".
-- DOI: 10.1017/S0305004100022684.
--
-- Author: John E. Hutchinson.
-- Title: "Fractals and self-similarity".
-- DOI: 10.1512/iumj.1981.30.30055.
--
-- ROUND75 / CRITICAL ANTICHAIN NO-GO
--
-- Round74 proved that an irregular row with
--
--     sum_i r_i^2 = 1
--
-- preserves the parent's squared amplification floor exactly.  The first
-- Round75 Moran/Hutchinson boundary showed that sibling separation does not
-- authorize parent+child cross-generation charge addition.
--
-- Therefore a SAFE antichain-only propagation argument at exact criticality
-- cannot make its floor exceed a budget which already funds the parent
-- generation: the next generation has exactly the same floor mass.
--
-- This is a useful falsifier.  `CumulativeIrregularSquaredFloorsOutrunBudget`
-- cannot be proved from critical S(e)=1 plus sibling non-overlap alone.  The
-- physical proof must establish at least one of:
--
--   A. genuine cross-generation additive charge, allowing different
--      generations to be summed; or
--   B. genuinely supercritical antichain growth, S(e)>1 often/strongly enough.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Data.Rational.Base using (ℚ; _≤_; _<_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst; sym)
open import Relation.Nullary.Negation.Core using (¬_)

import DASHI.Physics.Closure.NSTriadKNDeterministicIrregularSquaredCascadeRound74Exact as Cascade

criticalAntichainCannotOutrunParentBudget :
  ∀ (rows : List Cascade.CriticalSquaredPropagationRow) {budget : ℚ} →
  Cascade.criticalParentMass rows ≤ budget →
  Cascade.criticalChildMass rows ≤ budget
criticalAntichainCannotOutrunParentBudget rows parentWithinBudget =
  subst
    (_≤ _)
    (sym (Cascade.criticalIrregularGenerationPreservesSquaredFloor rows))
    parentWithinBudget

criticalAntichainAboveBudgetImpliesParentWasAlreadyAboveBudget :
  ∀ (rows : List Cascade.CriticalSquaredPropagationRow) {budget : ℚ} →
  budget < Cascade.criticalChildMass rows →
  budget < Cascade.criticalParentMass rows
criticalAntichainAboveBudgetImpliesParentWasAlreadyAboveBudget rows childAbove =
  subst
    (_ <_)
    (Cascade.criticalIrregularGenerationPreservesSquaredFloor rows)
    childAbove

criticalAntichainCannotCreateContradictionFromFundedParent :
  ∀ (rows : List Cascade.CriticalSquaredPropagationRow) {budget : ℚ} →
  Cascade.criticalParentMass rows ≤ budget →
  ¬ (budget < Cascade.criticalChildMass rows)
criticalAntichainCannotCreateContradictionFromFundedParent rows parentWithin childAbove =
  ℚP.<-irrefl budget
    (ℚP.<-≤-trans childAbove
      (criticalAntichainCannotOutrunParentBudget rows parentWithin))

round75CriticalAntichainAloneCannotOutrunBudget : Bool
round75CriticalAntichainAloneCannotOutrunBudget = true

round75C1NeedsCrossGenerationAdditivityOrSupercriticalAntichainGrowth : Bool
round75C1NeedsCrossGenerationAdditivityOrSupercriticalAntichainGrowth = true

round75CriticalAntichainAloneCannotOutrunBudgetIsTrue :
  round75CriticalAntichainAloneCannotOutrunBudget ≡ true
round75CriticalAntichainAloneCannotOutrunBudgetIsTrue = refl
