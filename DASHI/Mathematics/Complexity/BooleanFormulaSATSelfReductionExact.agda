module DASHI.Mathematics.Complexity.BooleanFormulaSATSelfReductionExact where

------------------------------------------------------------------------
-- FINITE-VARIABLE BOOLEAN SAT SELF-REDUCTION
--
-- Boolean formulas are indexed by the number of still-free variables.
-- Restricting variable zero to false/true lowers that index by one.  The
-- evaluator proves restriction correctness, satisfiability splits on the
-- chosen bit, and satisfying assignments lift back through each restriction.
--
-- Instantiating SATDecisionToWitnessSelfReductionExact therefore yields a
-- satisfying assignment for an n-variable satisfiable formula using exactly
-- n exact SAT-decision queries.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)
import Data.Fin.Base as Fin

import DASHI.Mathematics.Complexity.SATDecisionToWitnessSelfReductionExact as Search

notBool : Bool → Bool
notBool true = false
notBool false = true

andBool : Bool → Bool → Bool
andBool true right = right
andBool false right = false

orBool : Bool → Bool → Bool
orBool true right = true
orBool false right = right

data BooleanFormula (variables : Nat) : Set where
  variable : Fin.Fin variables → BooleanFormula variables
  constant : Bool → BooleanFormula variables
  negate : BooleanFormula variables → BooleanFormula variables
  conjunction disjunction :
    BooleanFormula variables →
    BooleanFormula variables →
    BooleanFormula variables

Assignment : Nat → Set
Assignment variables = Fin.Fin variables → Bool

evaluate :
  ∀ {variables} →
  BooleanFormula variables →
  Assignment variables →
  Bool
evaluate (variable index) assignment = assignment index
evaluate (constant value) assignment = value
evaluate (negate formula) assignment =
  notBool (evaluate formula assignment)
evaluate (conjunction left right) assignment =
  andBool (evaluate left assignment) (evaluate right assignment)
evaluate (disjunction left right) assignment =
  orBool (evaluate left assignment) (evaluate right assignment)

extendAssignment :
  ∀ {variables} →
  Bool →
  Assignment variables →
  Assignment (suc variables)
extendAssignment bit assignment Fin.zero = bit
extendAssignment bit assignment (Fin.suc index) = assignment index

tailAssignment :
  ∀ {variables} →
  Assignment (suc variables) →
  Assignment variables
tailAssignment assignment index = assignment (Fin.suc index)

restrictHead :
  ∀ {variables} →
  Bool →
  BooleanFormula (suc variables) →
  BooleanFormula variables
restrictHead bit (variable Fin.zero) = constant bit
restrictHead bit (variable (Fin.suc index)) = variable index
restrictHead bit (constant value) = constant value
restrictHead bit (negate formula) =
  negate (restrictHead bit formula)
restrictHead bit (conjunction left right) =
  conjunction (restrictHead bit left) (restrictHead bit right)
restrictHead bit (disjunction left right) =
  disjunction (restrictHead bit left) (restrictHead bit right)

restrictionEvaluation :
  ∀ {variables}
    (bit : Bool)
    (formula : BooleanFormula (suc variables))
    (assignment : Assignment variables) →
  evaluate (restrictHead bit formula) assignment
  ≡ evaluate formula (extendAssignment bit assignment)
restrictionEvaluation bit (variable Fin.zero) assignment = refl
restrictionEvaluation bit (variable (Fin.suc index)) assignment = refl
restrictionEvaluation bit (constant value) assignment = refl
restrictionEvaluation bit (negate formula) assignment =
  cong notBool (restrictionEvaluation bit formula assignment)
restrictionEvaluation bit (conjunction left right) assignment =
  cong₂ andBool
    (restrictionEvaluation bit left assignment)
    (restrictionEvaluation bit right assignment)
restrictionEvaluation bit (disjunction left right) assignment =
  cong₂ orBool
    (restrictionEvaluation bit left assignment)
    (restrictionEvaluation bit right assignment)

evaluateExtensional :
  ∀ {variables}
    (formula : BooleanFormula variables)
    {left right : Assignment variables} →
  ((index : Fin.Fin variables) → left index ≡ right index) →
  evaluate formula left ≡ evaluate formula right
evaluateExtensional (variable index) agreement = agreement index
evaluateExtensional (constant value) agreement = refl
evaluateExtensional (negate formula) agreement =
  cong notBool (evaluateExtensional formula agreement)
evaluateExtensional (conjunction left right) agreement =
  cong₂ andBool
    (evaluateExtensional left agreement)
    (evaluateExtensional right agreement)
evaluateExtensional (disjunction left right) agreement =
  cong₂ orBool
    (evaluateExtensional left agreement)
    (evaluateExtensional right agreement)

record Satisfying
    {variables : Nat}
    (formula : BooleanFormula variables) : Set where
  constructor satisfying
  field
    assignment : Assignment variables
    evaluatesTrue : evaluate formula assignment ≡ true

open Satisfying public

satisfiableSplits :
  ∀ {variables}
    (formula : BooleanFormula (suc variables)) →
  Satisfying formula →
  Satisfying (restrictHead false formula) ⊎
  Satisfying (restrictHead true formula)
satisfiableSplits formula witness
    with assignment witness Fin.zero
... | false =
  inj₁
    (satisfying
      (tailAssignment (assignment witness))
      (trans
        (restrictionEvaluation
          false formula
          (tailAssignment (assignment witness)))
        (trans
          (evaluateExtensional formula rebuild)
          (evaluatesTrue witness))))
  where
    rebuild :
      (index : Fin.Fin (suc variables)) →
      extendAssignment false
        (tailAssignment (assignment witness)) index
      ≡ assignment witness index
    rebuild Fin.zero = refl
    rebuild (Fin.suc index) = refl
... | true =
  inj₂
    (satisfying
      (tailAssignment (assignment witness))
      (trans
        (restrictionEvaluation
          true formula
          (tailAssignment (assignment witness)))
        (trans
          (evaluateExtensional formula rebuild)
          (evaluatesTrue witness))))
  where
    rebuild :
      (index : Fin.Fin (suc variables)) →
      extendAssignment true
        (tailAssignment (assignment witness)) index
      ≡ assignment witness index
    rebuild Fin.zero = refl
    rebuild (Fin.suc index) = refl

liftFalse :
  ∀ {variables}
    (formula : BooleanFormula (suc variables)) →
  Satisfying (restrictHead false formula) →
  Satisfying formula
liftFalse formula witness =
  satisfying
    (extendAssignment false (assignment witness))
    (trans
      (sym
        (restrictionEvaluation
          false formula
          (assignment witness)))
      (evaluatesTrue witness))

liftTrue :
  ∀ {variables}
    (formula : BooleanFormula (suc variables)) →
  Satisfying (restrictHead true formula) →
  Satisfying formula
liftTrue formula witness =
  satisfying
    (extendAssignment true (assignment witness))
    (trans
      (sym
        (restrictionEvaluation
          true formula
          (assignment witness)))
      (evaluatesTrue witness))

booleanSATSelfReduction : Search.BinarySelfReduction
booleanSATSelfReduction = record
  { Search.Node = BooleanFormula
  ; Search.SatisfiableAt = Satisfying
  ; Search.Solution = Satisfying
  ; Search.chooseFalse = restrictHead false
  ; Search.chooseTrue = restrictHead true
  ; Search.satisfiableSplits = satisfiableSplits
  ; Search.terminalSolution = λ formula witness → witness
  ; Search.liftFalseSolution = liftFalse
  ; Search.liftTrueSolution = liftTrue
  }

SATDecisionOracle : Set₁
SATDecisionOracle =
  Search.ExactDecisionOracle booleanSATSelfReduction

recoverSatisfyingAssignment :
  (oracle : SATDecisionOracle) →
  ∀ {variables}
    (formula : BooleanFormula variables) →
  Satisfying formula →
  Search.SearchResult
    booleanSATSelfReduction
    variables
    formula
recoverSatisfyingAssignment oracle formula =
  Search.recoverWitness
    booleanSATSelfReduction
    oracle
    formula

satSearchUsesExactlyVariableCountQueries :
  (oracle : SATDecisionOracle) →
  ∀ {variables}
    (formula : BooleanFormula variables)
    (witness : Satisfying formula) →
  Search.decisionQueries
    (recoverSatisfyingAssignment oracle formula witness)
  ≡ variables
satSearchUsesExactlyVariableCountQueries oracle formula witness =
  Search.exactQueryCount
    (recoverSatisfyingAssignment oracle formula witness)
