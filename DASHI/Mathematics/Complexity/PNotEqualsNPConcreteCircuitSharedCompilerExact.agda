module DASHI.Mathematics.Complexity.PNotEqualsNPConcreteCircuitSharedCompilerExact where

------------------------------------------------------------------------
-- GENERIC CONCRETE CIRCUIT DAG -> SHARED BOOLEAN CONSTRAINT FORMULA
--
-- One fresh propositional variable is allocated to each concrete DAG gate.
-- Gate references become variables rather than recursively copied subformulas.
-- The program is compiled to one local equivalence constraint per gate.
--
-- This owner focuses on the RESOURCE theorem needed by the self-diagonal lane:
--
--   gateCount(C) <= nodeCount(sharedConstraints(C)).
--
-- Thus the standard auxiliary-variable encoding preserves DAG sharing, but it
-- cannot encode a circuit with more than N gates inside an N-node formula.
--
-- Semantic soundness/completeness for arbitrary gate programs is separable;
-- PNotEqualsNPConcreteCircuitSharedConstraintExact already gives a concrete
-- satisfiable shared encoding on the repeated-fanout family.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Empty using (⊥)
open import Data.Fin.Base using (Fin; toℕ) renaming (zero to fzero; suc to fsuc)
open import Data.Nat.Base using (_≤_; _<_; z≤n; s≤s)
import Data.Nat.Properties as NatP

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PNotEqualsNPConcreteBooleanCircuitDAGExact as Circuit
import DASHI.Mathematics.Complexity.PNotEqualsNPConcreteCircuitSharedConstraintExact as Shared
import DASHI.Mathematics.Complexity.PNotEqualsNPProgramDescriptionFormulaEmbeddingExact as FormulaSize

------------------------------------------------------------------------
-- Stable variable numbering.
--
-- Inputs use variables 0 .. inputs-1.
-- A gate created after exactly g earlier gates uses variable inputs+g.
-- Because gateWire fzero denotes the newest earlier gate, the recursive index
-- below maps references back to the creation-time variable number.
------------------------------------------------------------------------

gateVariableIndex :
  (inputs : Nat) →
  ∀ {gates : Nat} →
  Fin gates →
  Nat
gateVariableIndex inputs {suc gates} fzero =
  inputs + gates
gateVariableIndex inputs {suc gates} (fsuc index) =
  gateVariableIndex inputs index

wireVariableFormula :
  ∀ {inputs gates : Nat} →
  Circuit.WireRef inputs gates →
  Cook.BooleanFormula
wireVariableFormula (Circuit.inputWire index) =
  Cook.variable (toℕ index)
wireVariableFormula {inputs} (Circuit.gateWire index) =
  Cook.variable (gateVariableIndex inputs index)

gateExpressionFormula :
  ∀ {inputs gates : Nat} →
  Circuit.Gate inputs gates →
  Cook.BooleanFormula
gateExpressionFormula (Circuit.constantGate value) =
  Cook.constant value
gateExpressionFormula (Circuit.notGate source) =
  Cook.negate
    (wireVariableFormula source)
gateExpressionFormula (Circuit.andGate left right) =
  Cook.conjunction
    (wireVariableFormula left)
    (wireVariableFormula right)
gateExpressionFormula (Circuit.orGate left right) =
  Cook.disjunction
    (wireVariableFormula left)
    (wireVariableFormula right)

gateConstraintFormula :
  ∀ {inputs gates : Nat} →
  Circuit.Gate inputs gates →
  Cook.BooleanFormula
gateConstraintFormula {inputs} {gates} gate =
  Shared.equivalenceFormula
    (Cook.variable (inputs + gates))
    (gateExpressionFormula gate)

programSharedConstraints :
  ∀ {inputs gates : Nat} →
  Circuit.GateProgram inputs gates →
  Cook.BooleanFormula
programSharedConstraints Circuit.noGates =
  Cook.constant Cook.true
programSharedConstraints (Circuit.appendGate previous gate) =
  Cook.conjunction
    (programSharedConstraints previous)
    (gateConstraintFormula gate)

circuitSharedConstraints :
  ∀ {inputs : Nat} →
  Circuit.ConcreteBooleanCircuit inputs →
  Cook.BooleanFormula
circuitSharedConstraints circuit =
  programSharedConstraints
    (Circuit.program circuit)

------------------------------------------------------------------------
-- Every Boolean formula has at least one syntax node.
------------------------------------------------------------------------

formulaNodeCountPositive :
  (formula : Cook.BooleanFormula) →
  suc zero ≤ FormulaSize.formulaNodeCount formula
formulaNodeCountPositive (Cook.variable index) =
  s≤s z≤n
formulaNodeCountPositive (Cook.constant value) =
  s≤s z≤n
formulaNodeCountPositive (Cook.negate formula) =
  s≤s z≤n
formulaNodeCountPositive (Cook.conjunction left right) =
  s≤s z≤n
formulaNodeCountPositive (Cook.disjunction left right) =
  s≤s z≤n

------------------------------------------------------------------------
-- One local constraint per gate implies the shared syntax is at least the
-- structural gate count.
------------------------------------------------------------------------

gateCountBelowSharedConstraintNodeCount :
  ∀ {inputs gates : Nat}
    (program : Circuit.GateProgram inputs gates) →
  gates ≤
  FormulaSize.formulaNodeCount
    (programSharedConstraints program)
gateCountBelowSharedConstraintNodeCount Circuit.noGates =
  z≤n
gateCountBelowSharedConstraintNodeCount
    (Circuit.appendGate previous gate) =
  s≤s
    (NatP.≤-trans
      (gateCountBelowSharedConstraintNodeCount previous)
      (NatP.m≤m+n
        (FormulaSize.formulaNodeCount
          (programSharedConstraints previous))
        (FormulaSize.formulaNodeCount
          (gateConstraintFormula gate))))

circuitGateCountBelowSharedConstraintNodeCount :
  ∀ {inputs : Nat}
    (circuit : Circuit.ConcreteBooleanCircuit inputs) →
  Circuit.circuitSize circuit
  ≤
  FormulaSize.formulaNodeCount
    (circuitSharedConstraints circuit)
circuitGateCountBelowSharedConstraintNodeCount circuit =
  gateCountBelowSharedConstraintNodeCount
    (Circuit.program circuit)

------------------------------------------------------------------------
-- Fixed-size self-encoding no-go for the standard shared compiler.
--
-- If the target claims the compiled constraint formula itself has size N while
-- the concrete circuit has strictly more than N gates, the gate-count lower
-- bound forces N < N.
------------------------------------------------------------------------

sharedConstraintCompilerCannotCloseBelowGateCount :
  ∀ {inputs : Nat}
    (circuit : Circuit.ConcreteBooleanCircuit inputs)
    (targetSize : Nat) →
  FormulaSize.formulaNodeCount
      (circuitSharedConstraints circuit)
    ≡ targetSize →
  targetSize < Circuit.circuitSize circuit →
  ⊥
sharedConstraintCompilerCannotCloseBelowGateCount
    circuit targetSize sizeExact targetBelowGates =
  NatP.<-irrefl
    targetSize
    (NatP.<-≤-trans
      targetBelowGates
      gatesBelowTarget)
  where
    gatesBelowTarget :
      Circuit.circuitSize circuit ≤ targetSize
    gatesBelowTarget =
      NatP.≤-trans
        (circuitGateCountBelowSharedConstraintNodeCount circuit)
        (NatP.≤-reflexive sizeExact)

------------------------------------------------------------------------
-- Family form: the standard gate-variable encoding cannot provide a
-- same-size diagonal object at any width where the selected circuit is already
-- larger than that width.
------------------------------------------------------------------------

sharedConstraintFamilyCannotSelfEncodeSuperlinearMember :
  (family : Circuit.ConcreteCircuitFamily)
  (inputWidth : Nat) →
  inputWidth
    < Circuit.circuitSize
        (Circuit.circuitAtWidth family inputWidth) →
  FormulaSize.formulaNodeCount
      (circuitSharedConstraints
        (Circuit.circuitAtWidth family inputWidth))
    ≡ inputWidth →
  ⊥
sharedConstraintFamilyCannotSelfEncodeSuperlinearMember
    family inputWidth circuitLarger sizeExact =
  sharedConstraintCompilerCannotCloseBelowGateCount
    (Circuit.circuitAtWidth family inputWidth)
    inputWidth
    sizeExact
    circuitLarger
