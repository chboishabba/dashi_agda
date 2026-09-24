module DASHI.Mathematics.Complexity.PNotEqualsNPSATSelfReductionSizeNoGoExact where

------------------------------------------------------------------------
-- SAT SELF-REDUCTION LOWERS VARIABLE COUNT, NOT SYNTAX SIZE
--
-- Existing owner:
--   BooleanFormulaSATSelfReductionExact
--
-- Restricting the head variable lowers the formula index from n+1 to n and is
-- enough for the standard decision-to-search reduction.  But structurally it
-- traverses the whole syntax tree and replaces occurrences of the chosen
-- variable by constants.
--
-- Main theorem:
--
--   nodeCount (restrictHead bit phi) = nodeCount phi.
--
-- Therefore ordinary SAT self-reducibility is well-founded in FREE-VARIABLE
-- COUNT while leaving the ordinary syntax-node size unchanged.  It does not
-- by itself provide the strictly-smaller self-instance required by the
-- resource-bounded diagonal recurrence.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc; _+_)
open import Relation.Binary.PropositionalEquality using (cong; cong₂)

import DASHI.Mathematics.Complexity.BooleanFormulaSATSelfReductionExact as SAT

------------------------------------------------------------------------
-- Structural node count on the indexed BooleanFormula carrier.
------------------------------------------------------------------------

formulaNodeCount :
  ∀ {variables : Nat} →
  SAT.BooleanFormula variables →
  Nat
formulaNodeCount (SAT.variable index) =
  suc 0
formulaNodeCount (SAT.constant value) =
  suc 0
formulaNodeCount (SAT.negate formula) =
  suc (formulaNodeCount formula)
formulaNodeCount (SAT.conjunction left right) =
  suc (formulaNodeCount left + formulaNodeCount right)
formulaNodeCount (SAT.disjunction left right) =
  suc (formulaNodeCount left + formulaNodeCount right)

------------------------------------------------------------------------
-- Exact size preservation under one variable restriction.
------------------------------------------------------------------------

restrictHeadPreservesNodeCount :
  ∀ {variables : Nat}
    (bit : Bool)
    (formula : SAT.BooleanFormula (suc variables)) →
  formulaNodeCount
    (SAT.restrictHead bit formula)
  ≡
  formulaNodeCount formula
restrictHeadPreservesNodeCount bit (SAT.variable index)
    with index
... | SAT.Fin.zero =
  refl
... | SAT.Fin.suc rest =
  refl
restrictHeadPreservesNodeCount bit (SAT.constant value) =
  refl
restrictHeadPreservesNodeCount bit (SAT.negate formula)
    rewrite restrictHeadPreservesNodeCount bit formula =
  refl
restrictHeadPreservesNodeCount bit (SAT.conjunction left right)
    rewrite restrictHeadPreservesNodeCount bit left
          | restrictHeadPreservesNodeCount bit right =
  refl
restrictHeadPreservesNodeCount bit (SAT.disjunction left right)
    rewrite restrictHeadPreservesNodeCount bit left
          | restrictHeadPreservesNodeCount bit right =
  refl

------------------------------------------------------------------------
-- Both branches preserve ordinary syntax size.
------------------------------------------------------------------------

falseRestrictionPreservesNodeCount :
  ∀ {variables : Nat}
    (formula : SAT.BooleanFormula (suc variables)) →
  formulaNodeCount
    (SAT.restrictHead false formula)
  ≡
  formulaNodeCount formula
falseRestrictionPreservesNodeCount =
  restrictHeadPreservesNodeCount false

trueRestrictionPreservesNodeCount :
  ∀ {variables : Nat}
    (formula : SAT.BooleanFormula (suc variables)) →
  formulaNodeCount
    (SAT.restrictHead true formula)
  ≡
  formulaNodeCount formula
trueRestrictionPreservesNodeCount =
  restrictHeadPreservesNodeCount true

------------------------------------------------------------------------
-- Route-level consequence.
--
-- The standard SAT search self-reduction gives:
--
--   variables(phi|b) = variables(phi)-1
--
-- but:
--
--   nodes(phi|b) = nodes(phi).
--
-- Hence recursion on variable count does NOT automatically yield recursion on
-- the self-diagonal size parameter N.  Any useful "strictly smaller SAT call"
-- theorem must use a different size measure plus a proved bridge back to the
-- ordinary encoding size relevant to D's polynomial clock.
------------------------------------------------------------------------
