module DASHI.Mathematics.Complexity.PNotEqualsNPIndexedFormulaVariableReorderingExact where

------------------------------------------------------------------------
-- EXACT VARIABLE REORDERING FOR THE INDEXED SAT CARRIER
--
-- Quotient width is order-sensitive.  The Shannon/self-reduction carrier
-- always restricts variable zero first, so a chosen decomposition order should
-- be represented by first permuting the variable indices.
--
-- This owner supplies:
--
--   renameFormula : (Fin n -> Fin m) -> Formula n -> Formula m
--
-- and proves exact evaluation compatibility.
--
-- For a bijective variable permutation on Fin n it proves satisfiability
-- equivalence in both directions.  Therefore a P9 quotient may operate on a
-- reordered root without changing SAT truth.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Fin.Base using (Fin)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Mathematics.Complexity.BooleanFormulaSATSelfReductionExact as SAT
import DASHI.Mathematics.Complexity.PNotEqualsNPCookIndexedFormulaBridgeExact as Bridge
import DASHI.Mathematics.Complexity.PNotEqualsNPProgramDescriptionFormulaEmbeddingExact as Size

------------------------------------------------------------------------
-- Generic variable renaming.
------------------------------------------------------------------------

renameFormula :
  ∀ {sourceVariables targetVariables : Nat} →
  (Fin sourceVariables → Fin targetVariables) →
  SAT.BooleanFormula sourceVariables →
  SAT.BooleanFormula targetVariables
renameFormula rename (SAT.variable index) =
  SAT.variable (rename index)
renameFormula rename (SAT.constant value) =
  SAT.constant value
renameFormula rename (SAT.negate formula) =
  SAT.negate
    (renameFormula rename formula)
renameFormula rename (SAT.conjunction left right) =
  SAT.conjunction
    (renameFormula rename left)
    (renameFormula rename right)
renameFormula rename (SAT.disjunction left right) =
  SAT.disjunction
    (renameFormula rename left)
    (renameFormula rename right)

renameAssignment :
  ∀ {sourceVariables targetVariables : Nat} →
  (Fin sourceVariables → Fin targetVariables) →
  SAT.Assignment targetVariables →
  SAT.Assignment sourceVariables
renameAssignment rename assignment index =
  assignment (rename index)

renameEvaluation :
  ∀ {sourceVariables targetVariables : Nat}
    (rename : Fin sourceVariables → Fin targetVariables)
    (formula : SAT.BooleanFormula sourceVariables)
    (assignment : SAT.Assignment targetVariables) →
  SAT.evaluate
    (renameFormula rename formula)
    assignment
  ≡
  SAT.evaluate
    formula
    (renameAssignment rename assignment)
renameEvaluation rename (SAT.variable index) assignment =
  refl
renameEvaluation rename (SAT.constant value) assignment =
  refl
renameEvaluation rename (SAT.negate formula) assignment =
  cong
    SAT.notBool
    (renameEvaluation rename formula assignment)
renameEvaluation rename (SAT.conjunction left right) assignment =
  cong₂
    SAT.andBool
    (renameEvaluation rename left assignment)
    (renameEvaluation rename right assignment)
renameEvaluation rename (SAT.disjunction left right) assignment =
  cong₂
    SAT.orBool
    (renameEvaluation rename left assignment)
    (renameEvaluation rename right assignment)

------------------------------------------------------------------------
-- Finite variable permutation.
------------------------------------------------------------------------

record VariablePermutation
    (variables : Nat) : Set₁ where
  constructor variable-permutation
  field
    forward :
      Fin variables →
      Fin variables

    backward :
      Fin variables →
      Fin variables

    backwardForward :
      (index : Fin variables) →
      backward (forward index)
      ≡ index

    forwardBackward :
      (index : Fin variables) →
      forward (backward index)
      ≡ index

open VariablePermutation public

renameByPermutation :
  ∀ {variables : Nat} →
  VariablePermutation variables →
  SAT.BooleanFormula variables →
  SAT.BooleanFormula variables
renameByPermutation permutation =
  renameFormula
    (forward permutation)

------------------------------------------------------------------------
-- Satisfiability preservation.
------------------------------------------------------------------------

permutationPreservesSatisfiabilityForward :
  ∀ {variables : Nat}
    (permutation : VariablePermutation variables)
    (formula : SAT.BooleanFormula variables) →
  SAT.Satisfying formula →
  SAT.Satisfying
    (renameByPermutation
      permutation
      formula)
permutationPreservesSatisfiabilityForward
    permutation
    formula
    (SAT.satisfying assignment evaluatesTrue) =
  SAT.satisfying
    reorderedAssignment
    (trans
      (renameEvaluation
        (forward permutation)
        formula
        reorderedAssignment)
      (trans
        (SAT.evaluateExtensional
          formula
          agreement)
        evaluatesTrue))
  where
    reorderedAssignment :
      SAT.Assignment variables
    reorderedAssignment index =
      assignment
        (backward permutation index)

    agreement :
      (index : Fin variables) →
      renameAssignment
        (forward permutation)
        reorderedAssignment
        index
      ≡ assignment index
    agreement index =
      cong
        assignment
        (backwardForward
          permutation
          index)

permutationPreservesSatisfiabilityBackward :
  ∀ {variables : Nat}
    (permutation : VariablePermutation variables)
    (formula : SAT.BooleanFormula variables) →
  SAT.Satisfying
    (renameByPermutation
      permutation
      formula) →
  SAT.Satisfying formula
permutationPreservesSatisfiabilityBackward
    permutation
    formula
    (SAT.satisfying assignment evaluatesTrue) =
  SAT.satisfying
    (renameAssignment
      (forward permutation)
      assignment)
    (trans
      (sym
        (renameEvaluation
          (forward permutation)
          formula
          assignment))
      evaluatesTrue)

------------------------------------------------------------------------
-- Exact satisfiability equivalence package.
------------------------------------------------------------------------

record ReorderingPreservesSAT
    {variables : Nat}
    (permutation : VariablePermutation variables)
    (formula : SAT.BooleanFormula variables) : Set where
  constructor reordering-preserves-sat
  field
    originalToReordered :
      SAT.Satisfying formula →
      SAT.Satisfying
        (renameByPermutation
          permutation
          formula)

    reorderedToOriginal :
      SAT.Satisfying
        (renameByPermutation
          permutation
          formula) →
      SAT.Satisfying formula

open ReorderingPreservesSAT public

reorderingPreservesSAT :
  ∀ {variables : Nat}
    (permutation : VariablePermutation variables)
    (formula : SAT.BooleanFormula variables) →
  ReorderingPreservesSAT
    permutation
    formula
reorderingPreservesSAT permutation formula =
  reordering-preserves-sat
    (permutationPreservesSatisfiabilityForward
      permutation
      formula)
    (permutationPreservesSatisfiabilityBackward
      permutation
      formula)

------------------------------------------------------------------------
-- Reordering changes variable names only, not ordinary Cook syntax-node count.
------------------------------------------------------------------------

reorderingPreservesCookNodeCount :
  ∀ {variables : Nat}
    (permutation : VariablePermutation variables)
    (formula : SAT.BooleanFormula variables) →
  Size.formulaNodeCount
    (Bridge.indexedToCook
      (renameByPermutation
        permutation
        formula))
  ≡
  Size.formulaNodeCount
    (Bridge.indexedToCook formula)
reorderingPreservesCookNodeCount
    permutation
    (SAT.variable index) =
  refl
reorderingPreservesCookNodeCount
    permutation
    (SAT.constant value) =
  refl
reorderingPreservesCookNodeCount
    permutation
    (SAT.negate formula)
    rewrite
      reorderingPreservesCookNodeCount
        permutation
        formula =
  refl
reorderingPreservesCookNodeCount
    permutation
    (SAT.conjunction left right)
    rewrite
      reorderingPreservesCookNodeCount
        permutation
        left
      |
      reorderingPreservesCookNodeCount
        permutation
        right =
  refl
reorderingPreservesCookNodeCount
    permutation
    (SAT.disjunction left right)
    rewrite
      reorderingPreservesCookNodeCount
        permutation
        left
      |
      reorderingPreservesCookNodeCount
        permutation
        right =
  refl

------------------------------------------------------------------------
-- Research consequence.
--
-- P9 can now include the decomposition order as actual proof data:
--
--   Cook root
--     -> finite indexed root
--     -> proved variable permutation
--     -> reordered root
--     -> head-restriction quotient.
--
-- SAT truth is unchanged by the ordering step.  A successful route must still
-- construct a GOOD order cheaply from the special self-instantiation
-- structure; this owner only removes the representation obstacle.
------------------------------------------------------------------------
