module DASHI.Mathematics.Complexity.PNotEqualsNPCookIndexedFormulaBridgeExact where

------------------------------------------------------------------------
-- CLAY-CRITICAL COOK BOOLEANFORMULA <-> FINITE INDEXED SAT FORMULA
--
-- The self-diagonal owners use CookLevinCircuitGCTBoundary.BooleanFormula:
--
--   variable : Nat -> BooleanFormula.
--
-- The exact Shannon/self-reduction owners use the finite indexed carrier:
--
--   variable : Fin n -> BooleanFormula n.
--
-- P9 cannot honestly quotient partial assignments of the actual self-diagonal
-- formula until these are connected.
--
-- This owner supplies a same-object bridge:
--
--   * compute a finite variable bound from the Cook syntax;
--   * prove every variable occurrence lies below that bound;
--   * translate with Fin.fromℕ<, preserving repeated variable identity;
--   * translate back with Fin.toℕ;
--   * prove Cook -> indexed -> Cook is exactly the original syntax;
--   * prove evaluation agreement for every Cook assignment.
--
-- No SAT theorem or complexity assumption is used.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Fin.Base as Fin using (Fin; fromℕ<; toℕ)
import Data.Fin.Properties as FinP
open import Data.Nat.Base using (_≤_; _<_; _⊔_)
import Data.Nat.Properties as NatP
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.BooleanFormulaSATSelfReductionExact as SAT

------------------------------------------------------------------------
-- Finite variable bound.
------------------------------------------------------------------------

formulaVariableBound :
  Cook.BooleanFormula →
  Nat
formulaVariableBound (Cook.variable index) =
  suc index
formulaVariableBound (Cook.constant value) =
  zero
formulaVariableBound (Cook.negate formula) =
  formulaVariableBound formula
formulaVariableBound (Cook.conjunction left right) =
  formulaVariableBound left
  ⊔
  formulaVariableBound right
formulaVariableBound (Cook.disjunction left right) =
  formulaVariableBound left
  ⊔
  formulaVariableBound right

------------------------------------------------------------------------
-- Proof that every occurrence lies below a chosen finite bound.
------------------------------------------------------------------------

data VariablesBelow
    (bound : Nat) :
    Cook.BooleanFormula →
    Set where

  variableBelow :
    ∀ {index : Nat} →
    index < bound →
    VariablesBelow
      bound
      (Cook.variable index)

  constantBelow :
    ∀ {value : Bool} →
    VariablesBelow
      bound
      (Cook.constant value)

  negateBelow :
    ∀ {formula} →
    VariablesBelow bound formula →
    VariablesBelow
      bound
      (Cook.negate formula)

  conjunctionBelow :
    ∀ {left right} →
    VariablesBelow bound left →
    VariablesBelow bound right →
    VariablesBelow
      bound
      (Cook.conjunction left right)

  disjunctionBelow :
    ∀ {left right} →
    VariablesBelow bound left →
    VariablesBelow bound right →
    VariablesBelow
      bound
      (Cook.disjunction left right)

variablesBelowMonotone :
  ∀ {small large formula} →
  VariablesBelow small formula →
  small ≤ large →
  VariablesBelow large formula
variablesBelowMonotone
    (variableBelow indexBelow) small≤large =
  variableBelow
    (NatP.<-≤-trans indexBelow small≤large)
variablesBelowMonotone constantBelow small≤large =
  constantBelow
variablesBelowMonotone
    (negateBelow below) small≤large =
  negateBelow
    (variablesBelowMonotone below small≤large)
variablesBelowMonotone
    (conjunctionBelow left right) small≤large =
  conjunctionBelow
    (variablesBelowMonotone left small≤large)
    (variablesBelowMonotone right small≤large)
variablesBelowMonotone
    (disjunctionBelow left right) small≤large =
  disjunctionBelow
    (variablesBelowMonotone left small≤large)
    (variablesBelowMonotone right small≤large)

canonicalVariablesBelow :
  (formula : Cook.BooleanFormula) →
  VariablesBelow
    (formulaVariableBound formula)
    formula
canonicalVariablesBelow (Cook.variable index) =
  variableBelow
    (NatP.n<1+n index)
canonicalVariablesBelow (Cook.constant value) =
  constantBelow
canonicalVariablesBelow (Cook.negate formula) =
  negateBelow
    (canonicalVariablesBelow formula)
canonicalVariablesBelow
    (Cook.conjunction left right) =
  conjunctionBelow
    (variablesBelowMonotone
      (canonicalVariablesBelow left)
      (NatP.m≤m⊔n
        (formulaVariableBound left)
        (formulaVariableBound right)))
    (variablesBelowMonotone
      (canonicalVariablesBelow right)
      (NatP.n≤m⊔n
        (formulaVariableBound left)
        (formulaVariableBound right)))
canonicalVariablesBelow
    (Cook.disjunction left right) =
  disjunctionBelow
    (variablesBelowMonotone
      (canonicalVariablesBelow left)
      (NatP.m≤m⊔n
        (formulaVariableBound left)
        (formulaVariableBound right)))
    (variablesBelowMonotone
      (canonicalVariablesBelow right)
      (NatP.n≤m⊔n
        (formulaVariableBound left)
        (formulaVariableBound right)))

------------------------------------------------------------------------
-- Cook -> finite indexed translation.
------------------------------------------------------------------------

cookToIndexedWithBound :
  ∀ {bound : Nat}
    (formula : Cook.BooleanFormula) →
  VariablesBelow bound formula →
  SAT.BooleanFormula bound
cookToIndexedWithBound
    (Cook.variable index)
    (variableBelow indexBelow) =
  SAT.variable
    (Fin.fromℕ< indexBelow)
cookToIndexedWithBound
    (Cook.constant value)
    constantBelow =
  SAT.constant value
cookToIndexedWithBound
    (Cook.negate formula)
    (negateBelow below) =
  SAT.negate
    (cookToIndexedWithBound formula below)
cookToIndexedWithBound
    (Cook.conjunction left right)
    (conjunctionBelow leftBelow rightBelow) =
  SAT.conjunction
    (cookToIndexedWithBound left leftBelow)
    (cookToIndexedWithBound right rightBelow)
cookToIndexedWithBound
    (Cook.disjunction left right)
    (disjunctionBelow leftBelow rightBelow) =
  SAT.disjunction
    (cookToIndexedWithBound left leftBelow)
    (cookToIndexedWithBound right rightBelow)

cookToIndexed :
  (formula : Cook.BooleanFormula) →
  SAT.BooleanFormula
    (formulaVariableBound formula)
cookToIndexed formula =
  cookToIndexedWithBound
    formula
    (canonicalVariablesBelow formula)

------------------------------------------------------------------------
-- Finite indexed -> Cook translation.
------------------------------------------------------------------------

indexedToCook :
  ∀ {variables : Nat} →
  SAT.BooleanFormula variables →
  Cook.BooleanFormula
indexedToCook (SAT.variable index) =
  Cook.variable (Fin.toℕ index)
indexedToCook (SAT.constant value) =
  Cook.constant value
indexedToCook (SAT.negate formula) =
  Cook.negate
    (indexedToCook formula)
indexedToCook (SAT.conjunction left right) =
  Cook.conjunction
    (indexedToCook left)
    (indexedToCook right)
indexedToCook (SAT.disjunction left right) =
  Cook.disjunction
    (indexedToCook left)
    (indexedToCook right)

------------------------------------------------------------------------
-- Exact syntactic round-trip.
------------------------------------------------------------------------

indexedAfterCookWithBound :
  ∀ {bound : Nat}
    (formula : Cook.BooleanFormula)
    (below : VariablesBelow bound formula) →
  indexedToCook
    (cookToIndexedWithBound formula below)
  ≡ formula
indexedAfterCookWithBound
    (Cook.variable index)
    (variableBelow indexBelow)
    rewrite FinP.toℕ-fromℕ< indexBelow =
  refl
indexedAfterCookWithBound
    (Cook.constant value)
    constantBelow =
  refl
indexedAfterCookWithBound
    (Cook.negate formula)
    (negateBelow below)
    rewrite indexedAfterCookWithBound formula below =
  refl
indexedAfterCookWithBound
    (Cook.conjunction left right)
    (conjunctionBelow leftBelow rightBelow)
    rewrite indexedAfterCookWithBound left leftBelow
          | indexedAfterCookWithBound right rightBelow =
  refl
indexedAfterCookWithBound
    (Cook.disjunction left right)
    (disjunctionBelow leftBelow rightBelow)
    rewrite indexedAfterCookWithBound left leftBelow
          | indexedAfterCookWithBound right rightBelow =
  refl

indexedAfterCook :
  (formula : Cook.BooleanFormula) →
  indexedToCook
    (cookToIndexed formula)
  ≡ formula
indexedAfterCook formula =
  indexedAfterCookWithBound
    formula
    (canonicalVariablesBelow formula)

------------------------------------------------------------------------
-- Evaluation preservation from any Cook assignment.
------------------------------------------------------------------------

finiteAssignmentFromCook :
  ∀ {variables : Nat} →
  Cook.Assignment →
  SAT.Assignment variables
finiteAssignmentFromCook assignment index =
  assignment (Fin.toℕ index)

cookToIndexedEvaluation :
  ∀ {bound : Nat}
    (formula : Cook.BooleanFormula)
    (below : VariablesBelow bound formula)
    (assignment : Cook.Assignment) →
  SAT.evaluate
    (cookToIndexedWithBound formula below)
    (finiteAssignmentFromCook assignment)
  ≡
  Cook.evaluate formula assignment
cookToIndexedEvaluation
    (Cook.variable index)
    (variableBelow indexBelow)
    assignment
    rewrite FinP.toℕ-fromℕ< indexBelow =
  refl
cookToIndexedEvaluation
    (Cook.constant value)
    constantBelow
    assignment =
  refl
cookToIndexedEvaluation
    (Cook.negate formula)
    (negateBelow below)
    assignment =
  cong
    SAT.notBool
    (cookToIndexedEvaluation
      formula below assignment)
cookToIndexedEvaluation
    (Cook.conjunction left right)
    (conjunctionBelow leftBelow rightBelow)
    assignment =
  cong₂
    SAT.andBool
    (cookToIndexedEvaluation
      left leftBelow assignment)
    (cookToIndexedEvaluation
      right rightBelow assignment)
cookToIndexedEvaluation
    (Cook.disjunction left right)
    (disjunctionBelow leftBelow rightBelow)
    assignment =
  cong₂
    SAT.orBool
    (cookToIndexedEvaluation
      left leftBelow assignment)
    (cookToIndexedEvaluation
      right rightBelow assignment)

cookToIndexedEvaluationCanonical :
  (formula : Cook.BooleanFormula)
  (assignment : Cook.Assignment) →
  SAT.evaluate
    (cookToIndexed formula)
    (finiteAssignmentFromCook assignment)
  ≡
  Cook.evaluate formula assignment
cookToIndexedEvaluationCanonical formula assignment =
  cookToIndexedEvaluation
    formula
    (canonicalVariablesBelow formula)
    assignment

------------------------------------------------------------------------
-- Cook satisfiability therefore maps into indexed satisfiability.
------------------------------------------------------------------------

cookSatisfiableGivesIndexedSatisfying :
  (formula : Cook.BooleanFormula) →
  Cook.Satisfiable formula →
  SAT.Satisfying
    (cookToIndexed formula)
cookSatisfiableGivesIndexedSatisfying
    formula
    (Cook.satisfyingAssignment
      assignment
      evaluatesTrue) =
  SAT.satisfying
    (finiteAssignmentFromCook assignment)
    (trans
      (cookToIndexedEvaluationCanonical
        formula assignment)
      evaluatesTrue)

------------------------------------------------------------------------
-- Research consequence.
--
-- The Shannon/self-reduction machinery can now be applied to a finite indexed
-- view of the actual Clay-critical Cook formula without changing the formula
-- when translated back to Cook syntax.
--
-- What is still absent is a CONSTRUCTED self-diagonal formula family with
-- resource-bounded self-reference.  This bridge pays only the syntax mismatch;
-- it does not manufacture the missing fixed point.
------------------------------------------------------------------------
