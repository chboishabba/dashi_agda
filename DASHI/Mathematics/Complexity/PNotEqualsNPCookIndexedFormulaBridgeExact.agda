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

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Fin.Base as Fin using (Fin; fromℕ<; toℕ)
import Data.Fin.Properties as FinP
open import Data.Nat.Base using (_≤_; _<_; _⊔_)
import Data.Nat.Properties as NatP
open import Data.Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.BooleanFormulaSATSelfReductionExact as SAT
import DASHI.Mathematics.Complexity.SATDecisionToWitnessSelfReductionExact as Search
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.PNotEqualsNPClayCoreExact as Clay

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
-- The two formula modules expose extensionally identical Boolean operations.
------------------------------------------------------------------------

notBoolAgreement :
  (value : Bool) →
  SAT.notBool value ≡ Cook.notBool value
notBoolAgreement false = refl
notBoolAgreement true = refl

andBoolAgreement :
  (left right : Bool) →
  SAT.andBool left right
  ≡ Cook.andBool left right
andBoolAgreement false right = refl
andBoolAgreement true right = refl

orBoolAgreement :
  (left right : Bool) →
  SAT.orBool left right
  ≡ Cook.orBool left right
orBoolAgreement false right = refl
orBoolAgreement true right = refl

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
  trans
    (cong
      SAT.notBool
      (cookToIndexedEvaluation
        formula below assignment))
    (notBoolAgreement
      (Cook.evaluate formula assignment))
cookToIndexedEvaluation
    (Cook.conjunction left right)
    (conjunctionBelow leftBelow rightBelow)
    assignment =
  trans
    (cong₂
      SAT.andBool
      (cookToIndexedEvaluation
        left leftBelow assignment)
      (cookToIndexedEvaluation
        right rightBelow assignment))
    (andBoolAgreement
      (Cook.evaluate left assignment)
      (Cook.evaluate right assignment))
cookToIndexedEvaluation
    (Cook.disjunction left right)
    (disjunctionBelow leftBelow rightBelow)
    assignment =
  trans
    (cong₂
      SAT.orBool
      (cookToIndexedEvaluation
        left leftBelow assignment)
      (cookToIndexedEvaluation
        right rightBelow assignment))
    (orBoolAgreement
      (Cook.evaluate left assignment)
      (Cook.evaluate right assignment))

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


------------------------------------------------------------------------
-- Extend a finite assignment to the total Nat-indexed Cook assignment.
------------------------------------------------------------------------

cookAssignmentFromFinite :
  ∀ {variables : Nat} →
  SAT.Assignment variables →
  Cook.Assignment
cookAssignmentFromFinite {zero} assignment index =
  false
cookAssignmentFromFinite {suc variables} assignment zero =
  assignment Fin.zero
cookAssignmentFromFinite {suc variables} assignment (suc index) =
  cookAssignmentFromFinite
    (λ inner → assignment (Fin.suc inner))
    index

cookAssignmentFromFiniteAgrees :
  ∀ {variables : Nat}
    (assignment : SAT.Assignment variables)
    (index : Fin variables) →
  cookAssignmentFromFinite assignment (Fin.toℕ index)
  ≡ assignment index
cookAssignmentFromFiniteAgrees
    {suc variables}
    assignment
    Fin.zero =
  refl
cookAssignmentFromFiniteAgrees
    {suc variables}
    assignment
    (Fin.suc index) =
  cookAssignmentFromFiniteAgrees
    (λ inner → assignment (Fin.suc inner))
    index

------------------------------------------------------------------------
-- Indexed -> Cook evaluation agreement.
------------------------------------------------------------------------

indexedToCookEvaluation :
  ∀ {variables : Nat}
    (formula : SAT.BooleanFormula variables)
    (assignment : SAT.Assignment variables) →
  Cook.evaluate
    (indexedToCook formula)
    (cookAssignmentFromFinite assignment)
  ≡
  SAT.evaluate formula assignment
indexedToCookEvaluation
    (SAT.variable index)
    assignment =
  cookAssignmentFromFiniteAgrees
    assignment
    index
indexedToCookEvaluation
    (SAT.constant value)
    assignment =
  refl
indexedToCookEvaluation
    (SAT.negate formula)
    assignment =
  trans
    (cong
      Cook.notBool
      (indexedToCookEvaluation
        formula assignment))
    (sym
      (notBoolAgreement
        (SAT.evaluate formula assignment)))
indexedToCookEvaluation
    (SAT.conjunction left right)
    assignment =
  trans
    (cong₂
      Cook.andBool
      (indexedToCookEvaluation
        left assignment)
      (indexedToCookEvaluation
        right assignment))
    (sym
      (andBoolAgreement
        (SAT.evaluate left assignment)
        (SAT.evaluate right assignment)))
indexedToCookEvaluation
    (SAT.disjunction left right)
    assignment =
  trans
    (cong₂
      Cook.orBool
      (indexedToCookEvaluation
        left assignment)
      (indexedToCookEvaluation
        right assignment))
    (sym
      (orBoolAgreement
        (SAT.evaluate left assignment)
        (SAT.evaluate right assignment)))

indexedToCookEvaluationFromCook :
  ∀ {variables : Nat}
    (formula : SAT.BooleanFormula variables)
    (assignment : Cook.Assignment) →
  Cook.evaluate
    (indexedToCook formula)
    assignment
  ≡
  SAT.evaluate
    formula
    (finiteAssignmentFromCook assignment)
indexedToCookEvaluationFromCook
    (SAT.variable index)
    assignment =
  refl
indexedToCookEvaluationFromCook
    (SAT.constant value)
    assignment =
  refl
indexedToCookEvaluationFromCook
    (SAT.negate formula)
    assignment =
  trans
    (cong
      Cook.notBool
      (indexedToCookEvaluationFromCook
        formula assignment))
    (sym
      (notBoolAgreement
        (SAT.evaluate
          formula
          (finiteAssignmentFromCook assignment))))
indexedToCookEvaluationFromCook
    (SAT.conjunction left right)
    assignment =
  trans
    (cong₂
      Cook.andBool
      (indexedToCookEvaluationFromCook
        left assignment)
      (indexedToCookEvaluationFromCook
        right assignment))
    (sym
      (andBoolAgreement
        (SAT.evaluate
          left
          (finiteAssignmentFromCook assignment))
        (SAT.evaluate
          right
          (finiteAssignmentFromCook assignment))))
indexedToCookEvaluationFromCook
    (SAT.disjunction left right)
    assignment =
  trans
    (cong₂
      Cook.orBool
      (indexedToCookEvaluationFromCook
        left assignment)
      (indexedToCookEvaluationFromCook
        right assignment))
    (sym
      (orBoolAgreement
        (SAT.evaluate
          left
          (finiteAssignmentFromCook assignment))
        (SAT.evaluate
          right
          (finiteAssignmentFromCook assignment))))

------------------------------------------------------------------------
-- Satisfiability equivalence for every indexed formula.
------------------------------------------------------------------------

indexedSatisfyingGivesCookSatisfiable :
  ∀ {variables : Nat}
    (formula : SAT.BooleanFormula variables) →
  SAT.Satisfying formula →
  Cook.Satisfiable
    (indexedToCook formula)
indexedSatisfyingGivesCookSatisfiable
    formula
    (SAT.satisfying assignment evaluatesTrue) =
  Cook.satisfyingAssignment
    (cookAssignmentFromFinite assignment)
    (trans
      (indexedToCookEvaluation
        formula assignment)
      evaluatesTrue)

cookSatisfiableIndexedFormulaGivesIndexedSatisfying :
  ∀ {variables : Nat}
    (formula : SAT.BooleanFormula variables) →
  Cook.Satisfiable
    (indexedToCook formula) →
  SAT.Satisfying formula
cookSatisfiableIndexedFormulaGivesIndexedSatisfying
    formula
    (Cook.satisfyingAssignment
      assignment evaluatesTrue) =
  SAT.satisfying
    (finiteAssignmentFromCook assignment)
    (trans
      (sym
        (indexedToCookEvaluationFromCook
          formula
          assignment))
      evaluatesTrue)

------------------------------------------------------------------------
-- Under SAT in P on the Clay-critical Cook carrier, obtain an exact decision
-- oracle on every finite indexed formula.
------------------------------------------------------------------------

indexedOracleFromCookInP :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula} →
  PR.InP cost Clay.SATLanguage →
  Search.ExactDecisionOracle
    SAT.booleanSATSelfReduction
indexedOracleFromCookInP satP = record
  { Search.decide =
      λ formula →
        PR.decide satP
          (indexedToCook formula)
  ; Search.sound =
      λ formula decidedTrue →
        cookSatisfiableIndexedFormulaGivesIndexedSatisfying
          formula
          (PR.sound satP
            (indexedToCook formula)
            decidedTrue)
  ; Search.complete =
      λ formula satisfiable →
        PR.complete satP
          (indexedToCook formula)
          (indexedSatisfyingGivesCookSatisfiable
            formula satisfiable)
  }

------------------------------------------------------------------------
-- Actual Cook formula -> indexed formula -> exact Shannon oracle lineage.
------------------------------------------------------------------------

cookFormulaIndexedView :
  Cook.BooleanFormula →
  Σ Nat
    (λ variables →
      SAT.BooleanFormula variables)
cookFormulaIndexedView formula =
  formulaVariableBound formula
  ,
  cookToIndexed formula

