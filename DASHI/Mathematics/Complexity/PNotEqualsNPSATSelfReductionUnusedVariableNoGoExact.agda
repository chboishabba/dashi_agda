module DASHI.Mathematics.Complexity.PNotEqualsNPSATSelfReductionUnusedVariableNoGoExact where

------------------------------------------------------------------------
-- UNUSED-VARIABLE SELF-REDUCTION NO-GO
--
-- The previous owners show that the repository's literal restrictHead
-- preserves syntax-node count.  This owner makes the obstruction semantic:
--
-- any n-variable formula can be weakened to an (n+1)-variable formula which
-- ignores the new head variable.  Restricting that unused variable, to either
-- false or true, recovers the original formula exactly.
--
-- Therefore no theorem of the form
--
--   "every SAT head-variable restriction produces a strictly smaller formula"
--
-- can hold universally.  The failure is not an artifact of the current
-- restriction implementation; the new variable may simply be semantically
-- irrelevant.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Fin.Base as Fin using (Fin; suc)
open import Relation.Binary.PropositionalEquality using (cong; cong₂)

import DASHI.Mathematics.Complexity.BooleanFormulaSATSelfReductionExact as SAT
import DASHI.Mathematics.Complexity.PNotEqualsNPSATSelfReductionSizeNoGoExact as Size

------------------------------------------------------------------------
-- Add one unused head variable by shifting all old variable indices.
------------------------------------------------------------------------

weakenFormula :
  ∀ {variables : Nat} →
  SAT.BooleanFormula variables →
  SAT.BooleanFormula (suc variables)
weakenFormula (SAT.variable index) =
  SAT.variable (Fin.suc index)
weakenFormula (SAT.constant value) =
  SAT.constant value
weakenFormula (SAT.negate formula) =
  SAT.negate (weakenFormula formula)
weakenFormula (SAT.conjunction left right) =
  SAT.conjunction
    (weakenFormula left)
    (weakenFormula right)
weakenFormula (SAT.disjunction left right) =
  SAT.disjunction
    (weakenFormula left)
    (weakenFormula right)

------------------------------------------------------------------------
-- Restricting the unused head variable is literally a left inverse.
------------------------------------------------------------------------

restrictWeakenFalse :
  ∀ {variables : Nat}
    (formula : SAT.BooleanFormula variables) →
  SAT.restrictHead false
    (weakenFormula formula)
  ≡ formula
restrictWeakenFalse (SAT.variable index) =
  refl
restrictWeakenFalse (SAT.constant value) =
  refl
restrictWeakenFalse (SAT.negate formula)
    rewrite restrictWeakenFalse formula =
  refl
restrictWeakenFalse (SAT.conjunction left right)
    rewrite restrictWeakenFalse left
          | restrictWeakenFalse right =
  refl
restrictWeakenFalse (SAT.disjunction left right)
    rewrite restrictWeakenFalse left
          | restrictWeakenFalse right =
  refl

restrictWeakenTrue :
  ∀ {variables : Nat}
    (formula : SAT.BooleanFormula variables) →
  SAT.restrictHead true
    (weakenFormula formula)
  ≡ formula
restrictWeakenTrue (SAT.variable index) =
  refl
restrictWeakenTrue (SAT.constant value) =
  refl
restrictWeakenTrue (SAT.negate formula)
    rewrite restrictWeakenTrue formula =
  refl
restrictWeakenTrue (SAT.conjunction left right)
    rewrite restrictWeakenTrue left
          | restrictWeakenTrue right =
  refl
restrictWeakenTrue (SAT.disjunction left right)
    rewrite restrictWeakenTrue left
          | restrictWeakenTrue right =
  refl

------------------------------------------------------------------------
-- Weakening itself preserves syntax size.
------------------------------------------------------------------------

weakenPreservesNodeCount :
  ∀ {variables : Nat}
    (formula : SAT.BooleanFormula variables) →
  Size.formulaNodeCount
    (weakenFormula formula)
  ≡
  Size.formulaNodeCount formula
weakenPreservesNodeCount (SAT.variable index) =
  refl
weakenPreservesNodeCount (SAT.constant value) =
  refl
weakenPreservesNodeCount (SAT.negate formula)
    rewrite weakenPreservesNodeCount formula =
  refl
weakenPreservesNodeCount (SAT.conjunction left right)
    rewrite weakenPreservesNodeCount left
          | weakenPreservesNodeCount right =
  refl
weakenPreservesNodeCount (SAT.disjunction left right)
    rewrite weakenPreservesNodeCount left
          | weakenPreservesNodeCount right =
  refl

------------------------------------------------------------------------
-- Research consequence.
--
-- SAT self-reducibility supplies well-founded descent in the number of free
-- variables, but there is no universal descent in semantic/syntactic instance
-- size: a newly exposed variable can be completely unused and restriction then
-- returns the original problem verbatim.
--
-- Any self-diagonal route based on "recursive calls on smaller SAT instances"
-- must prove a special size-descent theorem for its OWN generated family; the
-- generic SAT self-reduction theorem cannot supply it.
------------------------------------------------------------------------
