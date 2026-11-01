module DASHI.Mathematics.Complexity.BooleanFormulaFiniteSATDecisionExact where

------------------------------------------------------------------------
-- EXACT DECIDABILITY OF FINITE-VARIABLE BOOLEAN SAT
--
-- This is a computability-level sanity theorem for the P != NP diagonal lane.
-- SAT is decidable.  Therefore no self-reference theorem which applies to
-- EVERY total SAT decider can force
--
--   SAT(phi_D) <-> not D(phi_D).
--
-- The polynomial resource bound must do genuine mathematical work.
--
-- We decide the repository's finite-variable BooleanFormula recursively:
--
--   * zero free variables: evaluate the unique assignment;
--   * successor variables: decide both head restrictions;
--   * lift a branch witness when one exists;
--   * if both branches are impossible, satisfiableSplits refutes the parent.
--
-- No classical excluded middle or postulate is used.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (zero; suc)
open import Data.Empty using (⊥)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
import Data.Fin.Base as Fin
open import Relation.Binary.PropositionalEquality using (sym; trans)

import DASHI.Mathematics.Complexity.BooleanFormulaSATSelfReductionExact as SAT

falseNotTrue : false ≡ true → ⊥
falseNotTrue ()

SatisfiableDecision :
  ∀ {variables} →
  SAT.BooleanFormula variables →
  Set
SatisfiableDecision formula =
  SAT.Satisfying formula
  ⊎
  (SAT.Satisfying formula → ⊥)

emptyAssignment : SAT.Assignment zero
emptyAssignment ()

zeroVariableAssignmentUnique :
  (assignment : SAT.Assignment zero) →
  (index : Fin.Fin zero) →
  assignment index ≡ emptyAssignment index
zeroVariableAssignmentUnique assignment ()

decideZeroVariableSAT :
  (formula : SAT.BooleanFormula zero) →
  SatisfiableDecision formula
decideZeroVariableSAT formula
    with SAT.evaluate formula emptyAssignment
... | true =
  inj₁
    (SAT.satisfying emptyAssignment refl)
... | false =
  inj₂ refute
  where
    refute :
      SAT.Satisfying formula → ⊥
    refute witness =
      falseNotTrue
        (trans
          (SAT.evaluateExtensional
            formula
            (zeroVariableAssignmentUnique
              (SAT.assignment witness)))
          (SAT.evaluatesTrue witness))

decideFiniteSAT :
  ∀ {variables}
    (formula : SAT.BooleanFormula variables) →
  SatisfiableDecision formula
decideFiniteSAT {zero} formula =
  decideZeroVariableSAT formula
decideFiniteSAT {suc variables} formula
    with decideFiniteSAT (SAT.restrictHead false formula)
       | decideFiniteSAT (SAT.restrictHead true formula)
... | inj₁ falseWitness | trueDecision =
  inj₁
    (SAT.liftFalse formula falseWitness)
... | inj₂ falseImpossible | inj₁ trueWitness =
  inj₁
    (SAT.liftTrue formula trueWitness)
... | inj₂ falseImpossible | inj₂ trueImpossible =
  inj₂ refuteParent
  where
    refuteParent :
      SAT.Satisfying formula → ⊥
    refuteParent witness
        with SAT.satisfiableSplits formula witness
    ... | inj₁ falseWitness =
      falseImpossible falseWitness
    ... | inj₂ trueWitness =
      trueImpossible trueWitness

decideFiniteSATBool :
  ∀ {variables} →
  SAT.BooleanFormula variables →
  Bool
decideFiniteSATBool formula
    with decideFiniteSAT formula
... | inj₁ witness =
  true
... | inj₂ impossible =
  false

decideFiniteSATBoolSound :
  ∀ {variables}
    (formula : SAT.BooleanFormula variables) →
  decideFiniteSATBool formula ≡ true →
  SAT.Satisfying formula
decideFiniteSATBoolSound formula accepted
    with decideFiniteSAT formula
... | inj₁ witness =
  witness
... | inj₂ impossible =
  falseNotTrue accepted

decideFiniteSATBoolComplete :
  ∀ {variables}
    (formula : SAT.BooleanFormula variables) →
  SAT.Satisfying formula →
  decideFiniteSATBool formula ≡ true
decideFiniteSATBoolComplete formula witness
    with decideFiniteSAT formula
... | inj₁ found =
  refl
... | inj₂ impossible =
  absurd
  where
    absurd : false ≡ true
    absurd =
      caseImpossible (impossible witness)

    caseImpossible : ⊥ → false ≡ true
    caseImpossible ()


------------------------------------------------------------------------
-- Computability-level self-diagonal no-go.
--
-- A correct total SAT decider cannot admit a formula satisfying
--
--   SAT(phi) <-> decider(phi) = false.
--
-- This is the exact reason the proposed Clay route must exploit the
-- POLYNOMIAL resource restriction rather than a bare recursion theorem.
------------------------------------------------------------------------

correctFiniteSATDeciderBlocksSelfDiagonal :
  ∀ {variables}
    (formula : SAT.BooleanFormula variables) →
  (decideFiniteSATBool formula ≡ false →
    SAT.Satisfying formula) →
  (SAT.Satisfying formula →
    decideFiniteSATBool formula ≡ false) →
  ⊥
correctFiniteSATDeciderBlocksSelfDiagonal
    formula satisfiableIfRejects rejectsIfSatisfiable
    with decideFiniteSATBool formula
... | true =
  falseNotTrue
    (rejectsIfSatisfiable
      (decideFiniteSATBoolSound formula refl))
... | false =
  falseNotTrue
    (sym
      (decideFiniteSATBoolComplete
        formula
        (satisfiableIfRejects refl)))
