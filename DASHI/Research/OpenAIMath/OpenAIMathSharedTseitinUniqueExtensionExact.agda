module DASHI.Research.OpenAIMath.OpenAIMathSharedTseitinUniqueExtensionExact where

------------------------------------------------------------------------
-- SOURCE-FIRST, EXACT CARRIER: shared Boolean DAG -> Tseitin formula.
--
-- Existing original DASHI proof owners:
-- PNotEqualsNPConcreteCircuitSharedSemanticsExact (sound/complete semantics,
-- canonical assignment, all-gate realization), introduced via PR #1040
-- (opened 2026-09-24, merged by 2026-10-04).
-- PNotEqualsNPConcreteCircuitSharedUpperBoundExact owns formula syntax-node
-- upper bounds; this module does NOT re-prove them.
--
-- NEW: the existing realization and canonical-assignment proof imply that
-- every satisfying assignment has UNIQUE auxiliary gate values ON THE
-- FINITELY USED CIRCUIT COORDINATES, once input values are fixed.
-- This is the crucial parsimonious Tseitin ingredient, NOT yet a finite
-- enumeration/count bijection or OpenAI's bounded-width encoded-CNF theorem.
--
-- Historical prior art: Tseitin definitional circuit encodings, Cook-Levin.
-- OpenAI family 378 (October 2026) owns its separate fixed-machine exact
-- #SAT/runtime/space theorem. Never promote a Lean proof to Agda authority.
-- Source-written only; exact-head Agda kernel run pending; no ESD edits.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Fin.Base using (Fin)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PNotEqualsNPConcreteBooleanCircuitDAGExact as Circuit
import DASHI.Mathematics.Complexity.PNotEqualsNPConcreteCircuitSharedCompilerExact as Compiler
import DASHI.Mathematics.Complexity.PNotEqualsNPConcreteCircuitSharedSemanticsExact as Existing

-- Only these indices are constrained by the shared compiler. An arbitrary
-- Cook.Assignment is Nat -> Bool and has unconstrained tail coordinates.
-- A global equality of assignments would therefore be an invalid claim.
data UsedCircuitCoordinate (inputs gates : Nat) : Set where
  inputCoordinate : Fin inputs → UsedCircuitCoordinate inputs gates
  gateCoordinate : Fin gates → UsedCircuitCoordinate inputs gates

coordinateIndex :
  ∀ {inputs gates} → UsedCircuitCoordinate inputs gates → Nat
coordinateIndex (inputCoordinate i) = Data.Fin.Base.toℕ i
coordinateIndex {inputs = inputs} (gateCoordinate i) =
  Compiler.gateVariableIndex inputs i

-- Under shared constraints, the prior realization lemma forces each input
-- and auxiliary variable to match the prior canonical assignment.
canonicalAgreementOnUsedCoordinates :
  ∀ {inputs gates}
    (program : Circuit.GateProgram inputs gates)
    (assignment : Cook.Assignment)
    (constraintsHold :
      Cook.evaluate (Compiler.programSharedConstraints program) assignment
        ≡ true)
    (coordinate : UsedCircuitCoordinate inputs gates) →
  assignment (coordinateIndex coordinate) ≡
    Existing.assignmentFromProgram program
      (Existing.inputValues
        (Existing.sharedConstraintsGiveRealization
          program assignment constraintsHold))
      (coordinateIndex coordinate)
canonicalAgreementOnUsedCoordinates
    program assignment constraintsHold (inputCoordinate i) =
  trans
    (Existing.inputVariablesCorrect realization i)
    (sym
      (Existing.assignmentFromProgramInputCorrect
        program (Existing.inputValues realization) i))
  where
    realization =
      Existing.sharedConstraintsGiveRealization
        program assignment constraintsHold
canonicalAgreementOnUsedCoordinates
    program assignment constraintsHold (gateCoordinate i) =
  trans
    (Existing.gateVariablesCorrect realization i)
    (sym
      (Existing.assignmentFromProgramGateCorrect
        program (Existing.inputValues realization) i))
  where
    realization =
      Existing.sharedConstraintsGiveRealization
        program assignment constraintsHold

-- If two satisfying assignments have the same concrete circuit inputs,
-- the original gate semantics force identical values for EVERY auxiliary
-- gate. No arithmetic axioms, choice, or function-extensionality postulate.
uniqueAuxiliaryGateValues :
  ∀ {inputs gates}
    {program : Circuit.GateProgram inputs gates}
    {left right : Cook.Assignment}
    (leftRealization : Existing.ProgramAssignmentRealizes program left)
    (rightRealization : Existing.ProgramAssignmentRealizes program right)
    (sameInputVector :
      Existing.inputValues leftRealization
      ≡ Existing.inputValues rightRealization)
    (index : Fin gates) →
  left (Compiler.gateVariableIndex inputs index)
    ≡ right (Compiler.gateVariableIndex inputs index)
uniqueAuxiliaryGateValues
    {program = program}
    leftRealization rightRealization sameInputVector index =
  trans
    (Existing.gateVariablesCorrect leftRealization index)
    (trans
      (cong
        (λ values →
          Circuit.lookupVec index
            (Circuit.evaluateProgram program values))
        sameInputVector)
      (sym (Existing.gateVariablesCorrect rightRealization index)))

-- Together with the input coordinates, the extension is unique on all and
-- only the circuit variables that the compiler actually uses.
uniqueUsedCoordinates :
  ∀ {inputs gates}
    {program : Circuit.GateProgram inputs gates}
    {left right : Cook.Assignment}
    (leftRealization : Existing.ProgramAssignmentRealizes program left)
    (rightRealization : Existing.ProgramAssignmentRealizes program right)
    (sameInputVector :
      Existing.inputValues leftRealization
      ≡ Existing.inputValues rightRealization)
    (coordinate : UsedCircuitCoordinate inputs gates) →
  left (coordinateIndex coordinate) ≡ right (coordinateIndex coordinate)
uniqueUsedCoordinates
    leftRealization rightRealization sameInputVector
    (inputCoordinate i) =
  trans
    (Existing.inputVariablesCorrect leftRealization i)
    (trans
      (cong (Circuit.lookupVec i) sameInputVector)
      (sym (Existing.inputVariablesCorrect rightRealization i)))
uniqueUsedCoordinates
    leftRealization rightRealization sameInputVector
    (gateCoordinate i) =
  uniqueAuxiliaryGateValues
    leftRealization rightRealization sameInputVector i

------------------------------------------------------------------------
-- Lift the finite uniqueness statement to the ACTUAL shared acceptance
-- formula, reusing the existing Boolean conjunction proof. This is not a
-- theorem for a second, invented "SAT oracle" or a duplicate compiler.
------------------------------------------------------------------------

acceptedFormulaRealization :
  ∀ {inputs}
    (circuit : Circuit.ConcreteBooleanCircuit inputs)
    (assignment : Cook.Assignment)
    (accepted :
      Cook.evaluate (Existing.sharedAcceptanceFormula circuit) assignment
        ≡ true) →
  Existing.ProgramAssignmentRealizes
    (Circuit.program circuit) assignment
acceptedFormulaRealization circuit assignment accepted =
  Existing.sharedConstraintsGiveRealization
    (Circuit.program circuit)
    assignment
    (Existing.andTrueLeft accepted)

uniqueAcceptedFormulaModelsOnUsedCoordinates :
  ∀ {inputs}
    (circuit : Circuit.ConcreteBooleanCircuit inputs)
    (left right : Cook.Assignment)
    (leftAccepted :
      Cook.evaluate (Existing.sharedAcceptanceFormula circuit) left ≡ true)
    (rightAccepted :
      Cook.evaluate (Existing.sharedAcceptanceFormula circuit) right ≡ true)
    (sameInputs :
      Existing.inputValues
        (acceptedFormulaRealization circuit left leftAccepted)
        ≡
      Existing.inputValues
        (acceptedFormulaRealization circuit right rightAccepted))
    (coordinate :
      UsedCircuitCoordinate inputs (Circuit.gateCount circuit)) →
  left (coordinateIndex coordinate)
    ≡ right (coordinateIndex coordinate)
uniqueAcceptedFormulaModelsOnUsedCoordinates
    circuit left right leftAccepted rightAccepted sameInputs coordinate =
  uniqueUsedCoordinates
    (acceptedFormulaRealization circuit left leftAccepted)
    (acceptedFormulaRealization circuit right rightAccepted)
    sameInputs
    coordinate

-- Exact #SAT transfer remains strictly conditional on finite support,
-- a unique-extension bijection, a bounded-width CNF conversion, and
-- concrete encoded-bit/time/space accounting. This file pays the
-- functional-determination component, not the OpenAI machine theorem.
