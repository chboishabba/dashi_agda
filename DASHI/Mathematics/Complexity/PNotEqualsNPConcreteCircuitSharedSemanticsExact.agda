module DASHI.Mathematics.Complexity.PNotEqualsNPConcreteCircuitSharedSemanticsExact where

------------------------------------------------------------------------
-- GENERIC SEMANTIC EXACTNESS OF THE SHARED/TSEITIN CIRCUIT COMPILER
--
-- Existing owner:
--   PNotEqualsNPConcreteCircuitSharedCompilerExact
--
-- already compiles a concrete acyclic gate DAG into one fresh variable per
-- gate plus one local equivalence constraint per gate and proves the structural
-- size lower bound.
--
-- This owner pays the missing semantic theorem.
--
-- For every concrete circuit C:
--
--   sharedAcceptanceFormula(C)
--
-- is satisfiable iff there exists an input vector on which C evaluates true.
--
-- Thus the generic shared compiler is now a literal semantics-preserving SAT
-- bridge rather than only a resource accounting device.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin.Base as Fin using (Fin; toℕ)
import Data.Fin.Properties as FinP
open import Data.Nat.Base using (_<_; _≤_)
import Data.Nat.Properties as NatP
open import Data.Product using (Σ; _,_)
open import Data.Vec.Base using (Vec; []; _∷_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PNotEqualsNPConcreteBooleanCircuitDAGExact as Circuit
import DASHI.Mathematics.Complexity.PNotEqualsNPConcreteCircuitSharedConstraintExact as Shared
import DASHI.Mathematics.Complexity.PNotEqualsNPConcreteCircuitSharedCompilerExact as Compiler

------------------------------------------------------------------------
-- Small Boolean lemmas.
------------------------------------------------------------------------

andTrueLeft :
  ∀ {left right : Bool} →
  Cook.andBool left right ≡ true →
  left ≡ true
andTrueLeft {true} {true} proof = refl
andTrueLeft {true} {false} ()
andTrueLeft {false} {true} ()
andTrueLeft {false} {false} ()

andTrueRight :
  ∀ {left right : Bool} →
  Cook.andBool left right ≡ true →
  right ≡ true
andTrueRight {true} {true} proof = refl
andTrueRight {true} {false} ()
andTrueRight {false} {true} ()
andTrueRight {false} {false} ()

equivalenceTrueFromEqual :
  (left right : Bool) →
  left ≡ right →
  Cook.evaluate
    (Shared.equivalenceFormula
      (Cook.constant left)
      (Cook.constant right))
    (λ index → false)
  ≡ true
equivalenceTrueFromEqual false false refl = refl
equivalenceTrueFromEqual true true refl = refl

equivalenceTrueImpliesEqual :
  (left right : Bool) →
  Cook.evaluate
    (Shared.equivalenceFormula
      (Cook.constant left)
      (Cook.constant right))
    (λ index → false)
  ≡ true →
  left ≡ right
equivalenceTrueImpliesEqual false false proof = refl
equivalenceTrueImpliesEqual false true ()
equivalenceTrueImpliesEqual true false ()
equivalenceTrueImpliesEqual true true proof = refl

------------------------------------------------------------------------
-- Formula equivalence evaluates only through the values of its two operands.
------------------------------------------------------------------------

equivalenceEvaluation :
  (left right : Cook.BooleanFormula)
  (assignment : Cook.Assignment) →
  Cook.evaluate
    (Shared.equivalenceFormula left right)
    assignment
  ≡
  Cook.evaluate
    (Shared.equivalenceFormula
      (Cook.constant (Cook.evaluate left assignment))
      (Cook.constant (Cook.evaluate right assignment)))
    (λ index → false)
equivalenceEvaluation left right assignment
    with Cook.evaluate left assignment
       | Cook.evaluate right assignment
... | false | false = refl
... | false | true = refl
... | true | false = refl
... | true | true = refl

equivalenceConstraintTrueFromEqualValues :
  (left right : Cook.BooleanFormula)
  (assignment : Cook.Assignment) →
  Cook.evaluate left assignment
  ≡ Cook.evaluate right assignment →
  Cook.evaluate
    (Shared.equivalenceFormula left right)
    assignment
  ≡ true
equivalenceConstraintTrueFromEqualValues
    left right assignment equal =
  trans
    (equivalenceEvaluation left right assignment)
    (equivalenceTrueFromEqual
      (Cook.evaluate left assignment)
      (Cook.evaluate right assignment)
      equal)

equivalenceConstraintTrueImpliesEqualValues :
  (left right : Cook.BooleanFormula)
  (assignment : Cook.Assignment) →
  Cook.evaluate
    (Shared.equivalenceFormula left right)
    assignment
  ≡ true →
  Cook.evaluate left assignment
  ≡ Cook.evaluate right assignment
equivalenceConstraintTrueImpliesEqualValues
    left right assignment accepted =
  equivalenceTrueImpliesEqual
    (Cook.evaluate left assignment)
    (Cook.evaluate right assignment)
    (trans
      (sym (equivalenceEvaluation left right assignment))
      accepted)

------------------------------------------------------------------------
-- Finite vector tabulation from a Cook assignment.
------------------------------------------------------------------------

tabulateVec :
  ∀ {A : Set} {n : Nat} →
  (Fin n → A) →
  Vec A n
tabulateVec {n = zero} function =
  []
tabulateVec {n = suc n} function =
  function Fin.zero
  ∷
  tabulateVec
    (λ index → function (Fin.suc index))

lookupTabulateVec :
  ∀ {A : Set} {n : Nat}
    (function : Fin n → A)
    (index : Fin n) →
  Circuit.lookupVec
    index
    (tabulateVec function)
  ≡ function index
lookupTabulateVec {n = suc n} function Fin.zero =
  refl
lookupTabulateVec {n = suc n} function (Fin.suc index) =
  lookupTabulateVec
    (λ inner → function (Fin.suc inner))
    index

------------------------------------------------------------------------
-- Realization invariant for one assignment.
------------------------------------------------------------------------

record ProgramAssignmentRealizes
    {inputs gates : Nat}
    (program : Circuit.GateProgram inputs gates)
    (assignment : Cook.Assignment) : Set₁ where
  constructor program-assignment-realizes
  field
    inputValues :
      Vec Bool inputs

    inputVariablesCorrect :
      (index : Fin inputs) →
      assignment (Fin.toℕ index)
      ≡ Circuit.lookupVec index inputValues

    gateVariablesCorrect :
      (index : Fin gates) →
      assignment
        (Compiler.gateVariableIndex inputs index)
      ≡
      Circuit.lookupVec
        index
        (Circuit.evaluateProgram
          program
          inputValues)

open ProgramAssignmentRealizes public

------------------------------------------------------------------------
-- Every wire/gate formula denotes the corresponding circuit value under a
-- realizing assignment.
------------------------------------------------------------------------

wireFormulaCorrect :
  ∀ {inputs gates : Nat}
    {program : Circuit.GateProgram inputs gates}
    {assignment : Cook.Assignment}
    (realization : ProgramAssignmentRealizes program assignment)
    (wire : Circuit.WireRef inputs gates) →
  Cook.evaluate
    (Compiler.wireVariableFormula wire)
    assignment
  ≡
  Circuit.evaluateWire
    wire
    (inputValues realization)
    (Circuit.evaluateProgram
      program
      (inputValues realization))
wireFormulaCorrect realization (Circuit.inputWire index) =
  inputVariablesCorrect realization index
wireFormulaCorrect realization (Circuit.gateWire index) =
  gateVariablesCorrect realization index

gateExpressionCorrect :
  ∀ {inputs gates : Nat}
    {program : Circuit.GateProgram inputs gates}
    {assignment : Cook.Assignment} →
  ProgramAssignmentRealizes program assignment →
  (gate : Circuit.Gate inputs gates) →
  Cook.evaluate
    (Compiler.gateExpressionFormula gate)
    assignment
  ≡
  Circuit.evaluateGate
    gate
    (inputValues realization)
    (Circuit.evaluateProgram
      program
      (inputValues realization))
gateExpressionCorrect realization
    (Circuit.constantGate value) =
  refl
gateExpressionCorrect realization
    (Circuit.notGate source) =
  cong
    Cook.notBool
    (wireFormulaCorrect realization source)
gateExpressionCorrect realization
    (Circuit.andGate left right) =
  cong₂
    Cook.andBool
    (wireFormulaCorrect realization left)
    (wireFormulaCorrect realization right)
gateExpressionCorrect realization
    (Circuit.orGate left right) =
  cong₂
    Cook.orBool
    (wireFormulaCorrect realization left)
    (wireFormulaCorrect realization right)

------------------------------------------------------------------------
-- Restrict a realization of an appended program to its previous program.
------------------------------------------------------------------------

previousRealization :
  ∀ {inputs gates : Nat}
    {previous : Circuit.GateProgram inputs gates}
    {gate : Circuit.Gate inputs gates}
    {assignment : Cook.Assignment} →
  ProgramAssignmentRealizes
    (Circuit.appendGate previous gate)
    assignment →
  ProgramAssignmentRealizes
    previous
    assignment
previousRealization realization =
  program-assignment-realizes
    (inputValues realization)
    (inputVariablesCorrect realization)
    previousGateCorrect
  where
    previousGateCorrect :
      (index : Fin gates) →
      assignment
        (Compiler.gateVariableIndex inputs index)
      ≡
      Circuit.lookupVec
        index
        (Circuit.evaluateProgram
          previous
          (inputValues realization))
    previousGateCorrect index =
      gateVariablesCorrect
        realization
        (Fin.suc index)

------------------------------------------------------------------------
-- A realizing assignment satisfies all shared constraints.
------------------------------------------------------------------------

realizationSatisfiesSharedConstraints :
  ∀ {inputs gates : Nat}
    (program : Circuit.GateProgram inputs gates)
    (assignment : Cook.Assignment) →
  ProgramAssignmentRealizes program assignment →
  Cook.evaluate
    (Compiler.programSharedConstraints program)
    assignment
  ≡ true
realizationSatisfiesSharedConstraints
    Circuit.noGates
    assignment
    realization =
  refl
realizationSatisfiesSharedConstraints
    {inputs}
    {suc gates}
    (Circuit.appendGate previous gate)
    assignment
    realization =
  constraintsAndGate
  where
    previousAccepted :
      Cook.evaluate
        (Compiler.programSharedConstraints previous)
        assignment
      ≡ true
    previousAccepted =
      realizationSatisfiesSharedConstraints
        previous
        assignment
        (previousRealization realization)

    newestOutputCorrect :
      assignment (inputs + gates)
      ≡
      Circuit.evaluateGate
        gate
        (inputValues realization)
        (Circuit.evaluateProgram
          previous
          (inputValues realization))
    newestOutputCorrect =
      gateVariablesCorrect realization Fin.zero

    gateExpressionAccepted :
      Cook.evaluate
        (Compiler.gateExpressionFormula gate)
        assignment
      ≡
      Circuit.evaluateGate
        gate
        (inputValues realization)
        (Circuit.evaluateProgram
          previous
          (inputValues realization))
    gateExpressionAccepted =
      gateExpressionCorrect
        (previousRealization realization)
        gate

    gateConstraintAccepted :
      Cook.evaluate
        (Compiler.gateConstraintFormula gate)
        assignment
      ≡ true
    gateConstraintAccepted =
      equivalenceConstraintTrueFromEqualValues
        (Cook.variable (inputs + gates))
        (Compiler.gateExpressionFormula gate)
        assignment
        (trans
          newestOutputCorrect
          (sym gateExpressionAccepted))

    constraintsAndGate :
      Cook.evaluate
        (Compiler.programSharedConstraints
          (Circuit.appendGate previous gate))
        assignment
      ≡ true
    constraintsAndGate
      rewrite previousAccepted
            | gateConstraintAccepted =
      refl

------------------------------------------------------------------------
-- Conversely, satisfying all shared constraints forces gate semantics.
--
-- Inputs are read directly from the assignment.  The induction proves every
-- gate variable agrees with literal evaluateProgram.
------------------------------------------------------------------------

sharedConstraintsGiveRealization :
  ∀ {inputs gates : Nat}
    (program : Circuit.GateProgram inputs gates)
    (assignment : Cook.Assignment) →
  Cook.evaluate
    (Compiler.programSharedConstraints program)
    assignment
  ≡ true →
  ProgramAssignmentRealizes
    program
    assignment
sharedConstraintsGiveRealization
    {inputs}
    Circuit.noGates
    assignment
    accepted =
  program-assignment-realizes
    inputValues
    inputCorrect
    gateCorrect
  where
    inputValues :
      Vec Bool inputs
    inputValues =
      tabulateVec
        (λ index →
          assignment (Fin.toℕ index))

    inputCorrect :
      (index : Fin inputs) →
      assignment (Fin.toℕ index)
      ≡ Circuit.lookupVec index inputValues
    inputCorrect index =
      sym
        (lookupTabulateVec
          (λ inner →
            assignment (Fin.toℕ inner))
          index)

    gateCorrect :
      (index : Fin zero) →
      _
    gateCorrect ()
sharedConstraintsGiveRealization
    {inputs}
    {suc gates}
    (Circuit.appendGate previous gate)
    assignment
    accepted =
  program-assignment-realizes
    (inputValues previousRealization)
    (inputVariablesCorrect previousRealization)
    gateCorrect
  where
    previousAccepted :
      Cook.evaluate
        (Compiler.programSharedConstraints previous)
        assignment
      ≡ true
    previousAccepted =
      andTrueLeft accepted

    newestConstraintAccepted :
      Cook.evaluate
        (Compiler.gateConstraintFormula gate)
        assignment
      ≡ true
    newestConstraintAccepted =
      andTrueRight accepted

    previousRealization :
      ProgramAssignmentRealizes previous assignment
    previousRealization =
      sharedConstraintsGiveRealization
        previous
        assignment
        previousAccepted

    newestValueEqualExpression :
      assignment (inputs + gates)
      ≡
      Cook.evaluate
        (Compiler.gateExpressionFormula gate)
        assignment
    newestValueEqualExpression =
      equivalenceConstraintTrueImpliesEqualValues
        (Cook.variable (inputs + gates))
        (Compiler.gateExpressionFormula gate)
        assignment
        newestConstraintAccepted

    newestValueCorrect :
      assignment (inputs + gates)
      ≡
      Circuit.evaluateGate
        gate
        (inputValues previousRealization)
        (Circuit.evaluateProgram
          previous
          (inputValues previousRealization))
    newestValueCorrect =
      trans
        newestValueEqualExpression
        (gateExpressionCorrect
          previousRealization
          gate)

    gateCorrect :
      (index : Fin (suc gates)) →
      assignment
        (Compiler.gateVariableIndex inputs index)
      ≡
      Circuit.lookupVec
        index
        (Circuit.evaluateProgram
          (Circuit.appendGate previous gate)
          (inputValues previousRealization))
    gateCorrect Fin.zero =
      newestValueCorrect
    gateCorrect (Fin.suc index) =
      gateVariablesCorrect
        previousRealization
        index

------------------------------------------------------------------------
-- Canonical assignment construction for a given concrete input.
------------------------------------------------------------------------

natEqual : Nat → Nat → Bool
natEqual zero zero = true
natEqual zero (suc right) = false
natEqual (suc left) zero = false
natEqual (suc left) (suc right) =
  natEqual left right

natEqualRefl :
  (value : Nat) →
  natEqual value value ≡ true
natEqualRefl zero = refl
natEqualRefl (suc value) =
  natEqualRefl value

natEqualTrue :
  ∀ {left right : Nat} →
  natEqual left right ≡ true →
  left ≡ right
natEqualTrue {zero} {zero} proof = refl
natEqualTrue {zero} {suc right} ()
natEqualTrue {suc left} {zero} ()
natEqualTrue {suc left} {suc right} proof =
  cong suc
    (natEqualTrue proof)

updateAssignment :
  Nat →
  Bool →
  Cook.Assignment →
  Cook.Assignment
updateAssignment target value previous index
    with natEqual target index
... | true =
  value
... | false =
  previous index

updateAtSame :
  (target : Nat)
  (value : Bool)
  (previous : Cook.Assignment) →
  updateAssignment
    target
    value
    previous
    target
  ≡ value
updateAtSame target value previous
    rewrite natEqualRefl target =
  refl

updateAtDifferent :
  ∀ {target index : Nat}
    (value : Bool)
    (previous : Cook.Assignment) →
  (target ≡ index → ⊥) →
  updateAssignment
    target
    value
    previous
    index
  ≡ previous index
updateAtDifferent
    {target}
    {index}
    value
    previous
    different
    with natEqual target index
... | false =
  refl
... | true =
  ⊥-elim
    (different
      (natEqualTrue refl))

lookupNatVec :
  ∀ {n : Nat} →
  Nat →
  Vec Bool n →
  Bool
lookupNatVec index [] =
  false
lookupNatVec zero (value ∷ values) =
  value
lookupNatVec (suc index) (value ∷ values) =
  lookupNatVec index values

lookupNatVecAtFin :
  ∀ {n : Nat}
    (values : Vec Bool n)
    (index : Fin n) →
  lookupNatVec
    (Fin.toℕ index)
    values
  ≡
  Circuit.lookupVec index values
lookupNatVecAtFin
    (value ∷ values)
    Fin.zero =
  refl
lookupNatVecAtFin
    (value ∷ values)
    (Fin.suc index) =
  lookupNatVecAtFin
    values
    index

inputAssignment :
  ∀ {inputs : Nat} →
  Vec Bool inputs →
  Cook.Assignment
inputAssignment values index =
  lookupNatVec index values

gateVariableIndexBelowNext :
  ∀ (inputs : Nat)
    {gates : Nat}
    (index : Fin gates) →
  Compiler.gateVariableIndex inputs index
  <
  inputs + gates
gateVariableIndexBelowNext
    inputs
    {suc gates}
    Fin.zero =
  NatP.+-monoˡ-<
    inputs
    (NatP.n<1+n gates)
gateVariableIndexBelowNext
    inputs
    {suc gates}
    (Fin.suc index) =
  NatP.<-trans
    (gateVariableIndexBelowNext
      inputs
      index)
    (NatP.+-monoˡ-<
      inputs
      (NatP.n<1+n gates))

lessMakesReverseUnequal :
  ∀ {smaller larger : Nat} →
  smaller < larger →
  larger ≡ smaller →
  ⊥
lessMakesReverseUnequal smallerLess refl =
  NatP.<-irrefl _
    smallerLess

assignmentFromProgram :
  ∀ {inputs gates : Nat} →
  Circuit.GateProgram inputs gates →
  Vec Bool inputs →
  Cook.Assignment
assignmentFromProgram
    Circuit.noGates
    inputValues =
  inputAssignment inputValues
assignmentFromProgram
    {inputs}
    {suc gates}
    (Circuit.appendGate previous gate)
    inputValues =
  updateAssignment
    (inputs + gates)
    newestValue
    (assignmentFromProgram
      previous
      inputValues)
  where
    newestValue : Bool
    newestValue =
      Circuit.evaluateGate
        gate
        inputValues
        (Circuit.evaluateProgram
          previous
          inputValues)

assignmentFromProgramInputCorrect :
  ∀ {inputs gates : Nat}
    (program : Circuit.GateProgram inputs gates)
    (inputValues : Vec Bool inputs)
    (index : Fin inputs) →
  assignmentFromProgram
    program
    inputValues
    (Fin.toℕ index)
  ≡
  Circuit.lookupVec index inputValues
assignmentFromProgramInputCorrect
    Circuit.noGates
    inputValues
    index =
  lookupNatVecAtFin
    inputValues
    index
assignmentFromProgramInputCorrect
    {inputs}
    {suc gates}
    (Circuit.appendGate previous gate)
    inputValues
    index =
  trans
    unchanged
    (assignmentFromProgramInputCorrect
      previous
      inputValues
      index)
  where
    inputBelowNewGate :
      Fin.toℕ index
      <
      inputs + gates
    inputBelowNewGate =
      NatP.<-≤-trans
        (FinP.toℕ<n index)
        (NatP.m≤m+n inputs gates)

    unchanged :
      assignmentFromProgram
        (Circuit.appendGate previous gate)
        inputValues
        (Fin.toℕ index)
      ≡
      assignmentFromProgram
        previous
        inputValues
        (Fin.toℕ index)
    unchanged =
      updateAtDifferent
        _
        _
        (lessMakesReverseUnequal
          inputBelowNewGate)

assignmentFromProgramGateCorrect :
  ∀ {inputs gates : Nat}
    (program : Circuit.GateProgram inputs gates)
    (inputValues : Vec Bool inputs)
    (index : Fin gates) →
  assignmentFromProgram
    program
    inputValues
    (Compiler.gateVariableIndex inputs index)
  ≡
  Circuit.lookupVec
    index
    (Circuit.evaluateProgram
      program
      inputValues)
assignmentFromProgramGateCorrect
    Circuit.noGates
    inputValues
    ()
assignmentFromProgramGateCorrect
    {inputs}
    {suc gates}
    (Circuit.appendGate previous gate)
    inputValues
    Fin.zero =
  updateAtSame
    (inputs + gates)
    (Circuit.evaluateGate
      gate
      inputValues
      (Circuit.evaluateProgram
        previous
        inputValues))
    (assignmentFromProgram
      previous
      inputValues)
assignmentFromProgramGateCorrect
    {inputs}
    {suc gates}
    (Circuit.appendGate previous gate)
    inputValues
    (Fin.suc index) =
  trans
    unchanged
    (assignmentFromProgramGateCorrect
      previous
      inputValues
      index)
  where
    oldGateBelowNew :
      Compiler.gateVariableIndex inputs index
      <
      inputs + gates
    oldGateBelowNew =
      gateVariableIndexBelowNext
        inputs
        index

    unchanged :
      assignmentFromProgram
        (Circuit.appendGate previous gate)
        inputValues
        (Compiler.gateVariableIndex
          inputs
          (Fin.suc index))
      ≡
      assignmentFromProgram
        previous
        inputValues
        (Compiler.gateVariableIndex
          inputs
          index)
    unchanged =
      updateAtDifferent
        _
        _
        (lessMakesReverseUnequal
          oldGateBelowNew)

canonicalProgramRealization :
  ∀ {inputs gates : Nat}
    (program : Circuit.GateProgram inputs gates)
    (inputValues : Vec Bool inputs) →
  ProgramAssignmentRealizes
    program
    (assignmentFromProgram
      program
      inputValues)
canonicalProgramRealization program inputValues =
  program-assignment-realizes
    inputValues
    (assignmentFromProgramInputCorrect
      program
      inputValues)
    (assignmentFromProgramGateCorrect
      program
      inputValues)

------------------------------------------------------------------------
-- Output wire formula is exact under a realization.
------------------------------------------------------------------------

circuitOutputFormula :
  ∀ {inputs : Nat} →
  Circuit.ConcreteBooleanCircuit inputs →
  Cook.BooleanFormula
circuitOutputFormula circuit =
  Compiler.wireVariableFormula
    (Circuit.outputWire circuit)

sharedAcceptanceFormula :
  ∀ {inputs : Nat} →
  Circuit.ConcreteBooleanCircuit inputs →
  Cook.BooleanFormula
sharedAcceptanceFormula circuit =
  Cook.conjunction
    (Compiler.circuitSharedConstraints circuit)
    (circuitOutputFormula circuit)

canonicalOutputFormulaCorrect :
  ∀ {inputs : Nat}
    (circuit : Circuit.ConcreteBooleanCircuit inputs)
    (inputValues : Vec Bool inputs) →
  Cook.evaluate
    (circuitOutputFormula circuit)
    (assignmentFromProgram
      (Circuit.program circuit)
      inputValues)
  ≡
  Circuit.evaluateCircuit
    circuit
    inputValues
canonicalOutputFormulaCorrect circuit inputValues =
  wireFormulaCorrect
    (canonicalProgramRealization
      (Circuit.program circuit)
      inputValues)
    (Circuit.outputWire circuit)

------------------------------------------------------------------------
-- Completeness: accepted circuit input gives a SAT witness.
------------------------------------------------------------------------

acceptedInputGivesSharedSatisfiable :
  ∀ {inputs : Nat}
    (circuit : Circuit.ConcreteBooleanCircuit inputs)
    (inputValues : Vec Bool inputs) →
  Circuit.evaluateCircuit circuit inputValues
  ≡ true →
  Cook.Satisfiable
    (sharedAcceptanceFormula circuit)
acceptedInputGivesSharedSatisfiable
    circuit inputValues accepted =
  Cook.satisfyingAssignment
    assignment
    formulaAccepted
  where
    assignment : Cook.Assignment
    assignment =
      assignmentFromProgram
        (Circuit.program circuit)
        inputValues

    constraintsAccepted :
      Cook.evaluate
        (Compiler.circuitSharedConstraints circuit)
        assignment
      ≡ true
    constraintsAccepted =
      realizationSatisfiesSharedConstraints
        (Circuit.program circuit)
        assignment
        (canonicalProgramRealization
          (Circuit.program circuit)
          inputValues)

    outputAccepted :
      Cook.evaluate
        (circuitOutputFormula circuit)
        assignment
      ≡ true
    outputAccepted =
      trans
        (canonicalOutputFormulaCorrect
          circuit
          inputValues)
        accepted

    formulaAccepted :
      Cook.evaluate
        (sharedAcceptanceFormula circuit)
        assignment
      ≡ true
    formulaAccepted
      rewrite constraintsAccepted
            | outputAccepted =
      refl

------------------------------------------------------------------------
-- Soundness: SAT witness gives a concrete accepted circuit input.
------------------------------------------------------------------------

sharedSatisfiableGivesAcceptedInput :
  ∀ {inputs : Nat}
    (circuit : Circuit.ConcreteBooleanCircuit inputs) →
  Cook.Satisfiable
    (sharedAcceptanceFormula circuit) →
  Σ (Vec Bool inputs)
    (λ inputValues →
      Circuit.evaluateCircuit
        circuit
        inputValues
      ≡ true)
sharedSatisfiableGivesAcceptedInput
    circuit
    (Cook.satisfyingAssignment
      assignment
      accepted) =
  inputValues realization
  ,
  circuitAccepted
  where
    constraintsAccepted :
      Cook.evaluate
        (Compiler.circuitSharedConstraints circuit)
        assignment
      ≡ true
    constraintsAccepted =
      andTrueLeft accepted

    outputAccepted :
      Cook.evaluate
        (circuitOutputFormula circuit)
        assignment
      ≡ true
    outputAccepted =
      andTrueRight accepted

    realization :
      ProgramAssignmentRealizes
        (Circuit.program circuit)
        assignment
    realization =
      sharedConstraintsGiveRealization
        (Circuit.program circuit)
        assignment
        constraintsAccepted

    outputCorrect :
      Cook.evaluate
        (circuitOutputFormula circuit)
        assignment
      ≡
      Circuit.evaluateCircuit
        circuit
        (inputValues realization)
    outputCorrect =
      wireFormulaCorrect
        realization
        (Circuit.outputWire circuit)

    circuitAccepted :
      Circuit.evaluateCircuit
        circuit
        (inputValues realization)
      ≡ true
    circuitAccepted =
      trans
        (sym outputCorrect)
        outputAccepted

------------------------------------------------------------------------
-- Exact existential semantics.
------------------------------------------------------------------------

record SharedAcceptanceExact
    {inputs : Nat}
    (circuit : Circuit.ConcreteBooleanCircuit inputs) : Set₁ where
  constructor shared-acceptance-exact
  field
    circuitToSAT :
      (inputValues : Vec Bool inputs) →
      Circuit.evaluateCircuit circuit inputValues ≡ true →
      Cook.Satisfiable
        (sharedAcceptanceFormula circuit)

    satToCircuit :
      Cook.Satisfiable
        (sharedAcceptanceFormula circuit) →
      Σ (Vec Bool inputs)
        (λ inputValues →
          Circuit.evaluateCircuit circuit inputValues ≡ true)

open SharedAcceptanceExact public

sharedAcceptanceExact :
  ∀ {inputs : Nat}
    (circuit : Circuit.ConcreteBooleanCircuit inputs) →
  SharedAcceptanceExact circuit
sharedAcceptanceExact circuit =
  shared-acceptance-exact
    (acceptedInputGivesSharedSatisfiable circuit)
    (sharedSatisfiableGivesAcceptedInput circuit)

------------------------------------------------------------------------
-- Research consequence.
--
-- The generic concrete-DAG shared compiler is now semantically exact.  A
-- quotient DP may therefore be compiled to a concrete acyclic circuit and then
-- to an ordinary SAT formula without reopening a new semantic gap.
------------------------------------------------------------------------
