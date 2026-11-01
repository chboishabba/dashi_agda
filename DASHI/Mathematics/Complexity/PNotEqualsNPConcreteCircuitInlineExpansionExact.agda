module DASHI.Mathematics.Complexity.PNotEqualsNPConcreteCircuitInlineExpansionExact where

------------------------------------------------------------------------
-- CONCRETE CIRCUIT DAG -> ORDINARY BOOLEAN FORMULA BY NAIVE INLINING
--
-- This owner makes the sharing problem literal.
--
-- A concrete acyclic circuit can reuse an earlier gate at many later gates.
-- If we translate a gate reference by COPYING the referenced BooleanFormula,
-- that DAG sharing disappears.  The generic compiler below is semantically
-- correct, but a repeated-fanout family proves exact exponential tree growth.
--
-- Therefore:
--
--   small circuit DAG
--       does NOT imply
--   equally small ordinary formula under naive inline expansion.
--
-- Any self-evaluation route which wants linear/near-linear syntax must retain
-- sharing explicitly, e.g. through auxiliary gate variables / Tseitin-style
-- constraints, rather than recursively substituting gate definitions.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Fin.Base using (Fin; toℕ) renaming (zero to fzero; suc to fsuc)
open import Data.Vec.Base using (Vec; []; _∷_)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PNotEqualsNPConcreteBooleanCircuitDAGExact as Circuit
import DASHI.Mathematics.Complexity.PNotEqualsNPProgramDescriptionFormulaEmbeddingExact as FormulaSize

------------------------------------------------------------------------
-- Turn a finite Boolean input vector into a total formula assignment.
------------------------------------------------------------------------

assignmentFromVec :
  ∀ {inputs : Nat} →
  Vec Bool inputs →
  Cook.Assignment
assignmentFromVec [] index =
  false
assignmentFromVec (value ∷ rest) zero =
  value
assignmentFromVec (value ∷ rest) (suc index) =
  assignmentFromVec rest index

assignmentLookup :
  ∀ {inputs : Nat}
    (index : Fin inputs)
    (values : Vec Bool inputs) →
  assignmentFromVec values (toℕ index)
  ≡ Circuit.lookupVec index values
assignmentLookup fzero (value ∷ rest) =
  refl
assignmentLookup (fsuc index) (value ∷ rest) =
  assignmentLookup index rest

------------------------------------------------------------------------
-- Inline gate references as syntax trees.
------------------------------------------------------------------------

wireFormula :
  ∀ {inputs gates : Nat} →
  Circuit.WireRef inputs gates →
  Vec Cook.BooleanFormula gates →
  Cook.BooleanFormula
wireFormula (Circuit.inputWire index) gateFormulas =
  Cook.variable (toℕ index)
wireFormula (Circuit.gateWire index) gateFormulas =
  Circuit.lookupVec index gateFormulas

gateFormula :
  ∀ {inputs gates : Nat} →
  Circuit.Gate inputs gates →
  Vec Cook.BooleanFormula gates →
  Cook.BooleanFormula
gateFormula (Circuit.constantGate value) gateFormulas =
  Cook.constant value
gateFormula (Circuit.notGate source) gateFormulas =
  Cook.negate
    (wireFormula source gateFormulas)
gateFormula (Circuit.andGate left right) gateFormulas =
  Cook.conjunction
    (wireFormula left gateFormulas)
    (wireFormula right gateFormulas)
gateFormula (Circuit.orGate left right) gateFormulas =
  Cook.disjunction
    (wireFormula left gateFormulas)
    (wireFormula right gateFormulas)

compileProgramInline :
  ∀ {inputs gates : Nat} →
  Circuit.GateProgram inputs gates →
  Vec Cook.BooleanFormula gates
compileProgramInline Circuit.noGates =
  []
compileProgramInline (Circuit.appendGate previous gate) =
  gateFormula gate (compileProgramInline previous)
  ∷
  compileProgramInline previous

compileCircuitInline :
  ∀ {inputs : Nat} →
  Circuit.ConcreteBooleanCircuit inputs →
  Cook.BooleanFormula
compileCircuitInline circuit =
  wireFormula
    (Circuit.outputWire circuit)
    (compileProgramInline (Circuit.program circuit))

------------------------------------------------------------------------
-- Semantic correctness.
------------------------------------------------------------------------

wireFormulaCorrect :
  ∀ {inputs gates : Nat}
    (wire : Circuit.WireRef inputs gates)
    (inputValues : Vec Bool inputs)
    (gateFormulas : Vec Cook.BooleanFormula gates)
    (gateValues : Vec Bool gates) →
  ((index : Fin gates) →
    Cook.evaluate
      (Circuit.lookupVec index gateFormulas)
      (assignmentFromVec inputValues)
    ≡
    Circuit.lookupVec index gateValues) →
  Cook.evaluate
    (wireFormula wire gateFormulas)
    (assignmentFromVec inputValues)
  ≡
  Circuit.evaluateWire wire inputValues gateValues
wireFormulaCorrect
    (Circuit.inputWire index)
    inputValues gateFormulas gateValues gateCorrect =
  assignmentLookup index inputValues
wireFormulaCorrect
    (Circuit.gateWire index)
    inputValues gateFormulas gateValues gateCorrect =
  gateCorrect index

gateFormulaCorrect :
  ∀ {inputs gates : Nat}
    (gate : Circuit.Gate inputs gates)
    (inputValues : Vec Bool inputs)
    (gateFormulas : Vec Cook.BooleanFormula gates)
    (gateValues : Vec Bool gates) →
  ((index : Fin gates) →
    Cook.evaluate
      (Circuit.lookupVec index gateFormulas)
      (assignmentFromVec inputValues)
    ≡
    Circuit.lookupVec index gateValues) →
  Cook.evaluate
    (gateFormula gate gateFormulas)
    (assignmentFromVec inputValues)
  ≡
  Circuit.evaluateGate gate inputValues gateValues
gateFormulaCorrect
    (Circuit.constantGate value)
    inputValues gateFormulas gateValues gateCorrect =
  refl
gateFormulaCorrect
    (Circuit.notGate source)
    inputValues gateFormulas gateValues gateCorrect
    rewrite
      wireFormulaCorrect
        source inputValues gateFormulas gateValues gateCorrect =
  refl
gateFormulaCorrect
    (Circuit.andGate left right)
    inputValues gateFormulas gateValues gateCorrect
    rewrite
      wireFormulaCorrect
        left inputValues gateFormulas gateValues gateCorrect
      |
      wireFormulaCorrect
        right inputValues gateFormulas gateValues gateCorrect =
  refl
gateFormulaCorrect
    (Circuit.orGate left right)
    inputValues gateFormulas gateValues gateCorrect
    rewrite
      wireFormulaCorrect
        left inputValues gateFormulas gateValues gateCorrect
      |
      wireFormulaCorrect
        right inputValues gateFormulas gateValues gateCorrect =
  refl

programInlineCorrect :
  ∀ {inputs gates : Nat}
    (program : Circuit.GateProgram inputs gates)
    (inputValues : Vec Bool inputs)
    (index : Fin gates) →
  Cook.evaluate
    (Circuit.lookupVec index (compileProgramInline program))
    (assignmentFromVec inputValues)
  ≡
  Circuit.lookupVec index
    (Circuit.evaluateProgram program inputValues)
programInlineCorrect Circuit.noGates inputValues ()
programInlineCorrect
    (Circuit.appendGate previous gate)
    inputValues fzero =
  gateFormulaCorrect
    gate
    inputValues
    (compileProgramInline previous)
    (Circuit.evaluateProgram previous inputValues)
    (programInlineCorrect previous inputValues)
programInlineCorrect
    (Circuit.appendGate previous gate)
    inputValues (fsuc index) =
  programInlineCorrect previous inputValues index

compileCircuitInlineCorrect :
  ∀ {inputs : Nat}
    (circuit : Circuit.ConcreteBooleanCircuit inputs)
    (inputValues : Vec Bool inputs) →
  Cook.evaluate
    (compileCircuitInline circuit)
    (assignmentFromVec inputValues)
  ≡
  Circuit.evaluateCircuit circuit inputValues
compileCircuitInlineCorrect circuit inputValues =
  wireFormulaCorrect
    (Circuit.outputWire circuit)
    inputValues
    (compileProgramInline (Circuit.program circuit))
    (Circuit.evaluateProgram (Circuit.program circuit) inputValues)
    (programInlineCorrect (Circuit.program circuit) inputValues)

------------------------------------------------------------------------
-- Repeated-fanout family.
--
-- Each gate computes x AND x from the immediately previous wire.  The DAG has
-- exactly d gates.  Booleanly it still computes the original input bit.
------------------------------------------------------------------------

duplicatingProgram :
  (depth : Nat) →
  Circuit.GateProgram (suc zero) depth
duplicatingProgram zero =
  Circuit.noGates
duplicatingProgram (suc zero) =
  Circuit.appendGate
    Circuit.noGates
    (Circuit.andGate
      (Circuit.inputWire fzero)
      (Circuit.inputWire fzero))
duplicatingProgram (suc (suc depth)) =
  Circuit.appendGate
    (duplicatingProgram (suc depth))
    (Circuit.andGate
      (Circuit.gateWire fzero)
      (Circuit.gateWire fzero))

duplicatingCircuit :
  (depth : Nat) →
  Circuit.ConcreteBooleanCircuit (suc zero)
duplicatingCircuit zero =
  Circuit.concrete-boolean-circuit
    zero
    Circuit.noGates
    (Circuit.inputWire fzero)
duplicatingCircuit (suc depth) =
  Circuit.concrete-boolean-circuit
    (suc depth)
    (duplicatingProgram (suc depth))
    (Circuit.gateWire fzero)

duplicatingCircuitGateCount :
  (depth : Nat) →
  Circuit.circuitSize (duplicatingCircuit depth)
  ≡ depth
duplicatingCircuitGateCount depth =
  refl

------------------------------------------------------------------------
-- Exact inline syntax growth.
------------------------------------------------------------------------

duplicateInlineSize : Nat → Nat
duplicateInlineSize zero =
  suc zero
duplicateInlineSize (suc depth) =
  suc
    (duplicateInlineSize depth
     + duplicateInlineSize depth)

duplicatingInlineNodeCount :
  (depth : Nat) →
  FormulaSize.formulaNodeCount
    (compileCircuitInline (duplicatingCircuit depth))
  ≡
  duplicateInlineSize depth
duplicatingInlineNodeCount zero =
  refl
duplicatingInlineNodeCount (suc zero) =
  refl
duplicatingInlineNodeCount (suc (suc depth))
    rewrite duplicatingInlineNodeCount (suc depth) =
  refl

------------------------------------------------------------------------
-- The semantic computation did not become harder; only tree expansion did.
------------------------------------------------------------------------

duplicatingCircuitComputesInput :
  (depth : Nat)
  (value : Bool) →
  Circuit.evaluateCircuit
    (duplicatingCircuit depth)
    (value ∷ [])
  ≡ value
duplicatingCircuitComputesInput zero value =
  refl
duplicatingCircuitComputesInput (suc zero) true =
  refl
duplicatingCircuitComputesInput (suc zero) false =
  refl
duplicatingCircuitComputesInput (suc (suc depth)) value
    with
      Circuit.evaluateCircuit
        (duplicatingCircuit (suc depth))
        (value ∷ [])
      | duplicatingCircuitComputesInput (suc depth) value
... | .value | refl
    with value
... | true = refl
... | false = refl

------------------------------------------------------------------------
-- Consequence.
--
-- The circuit has d gates, while the naive inline formula obeys
--
--   S(0)=1
--   S(d+1)=1+2*S(d).
--
-- Thus gate-definition sharing is real at the DAG level, but ordinary formula
-- substitution duplicates every reused subgate.  A self-diagonal circuit route
-- therefore needs an auxiliary-variable / shared-constraint encoding rather
-- than inline expansion.
------------------------------------------------------------------------
