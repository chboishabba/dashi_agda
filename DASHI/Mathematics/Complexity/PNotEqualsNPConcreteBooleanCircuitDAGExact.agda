module DASHI.Mathematics.Complexity.PNotEqualsNPConcreteBooleanCircuitDAGExact where

------------------------------------------------------------------------
-- CONCRETE ACYCLIC BOOLEAN CIRCUIT DAG
--
-- The existing BooleanCircuitFamily boundary is intentionally permissive and
-- can assign size zero to an arbitrary extensional function.  This owner
-- supplies the minimal concrete replacement needed by the Clay-critical
-- self-diagonal lane:
--
--   * a fixed number of Boolean input wires;
--   * an acyclic straight-line gate program;
--   * each gate may reference only an input or an EARLIER gate;
--   * executable Boolean semantics;
--   * structural gate count, carried by the program index itself.
--
-- No machine -> circuit simulation theorem and no circuit lower bound is
-- asserted here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Fin.Base using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Vec.Base using (Vec; []; _∷_)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook

------------------------------------------------------------------------
-- Finite vector lookup, kept local to avoid relying on a library lookup name.
------------------------------------------------------------------------

lookupVec :
  ∀ {A : Set} {n : Nat} →
  Fin n →
  Vec A n →
  A
lookupVec fzero (value ∷ rest) =
  value
lookupVec (fsuc index) (value ∷ rest) =
  lookupVec index rest

------------------------------------------------------------------------
-- Wires available to a gate at construction depth g.
--
-- gateWire i refers only to one of the g already-constructed gates.
------------------------------------------------------------------------

data WireRef (inputs gates : Nat) : Set where
  inputWire :
    Fin inputs →
    WireRef inputs gates

  gateWire :
    Fin gates →
    WireRef inputs gates

data Gate (inputs gates : Nat) : Set where
  constantGate :
    Bool →
    Gate inputs gates

  notGate :
    WireRef inputs gates →
    Gate inputs gates

  andGate :
    WireRef inputs gates →
    WireRef inputs gates →
    Gate inputs gates

  orGate :
    WireRef inputs gates →
    WireRef inputs gates →
    Gate inputs gates

------------------------------------------------------------------------
-- Gate programs.
--
-- Outputs are stored newest-first.  Therefore fzero at the next construction
-- step refers to the immediately preceding gate, and fsuc walks backwards
-- through older gates.  This makes acyclicity structural.
------------------------------------------------------------------------

data GateProgram (inputs : Nat) : Nat → Set where
  noGates :
    GateProgram inputs zero

  appendGate :
    ∀ {gates : Nat} →
    GateProgram inputs gates →
    Gate inputs gates →
    GateProgram inputs (suc gates)

evaluateWire :
  ∀ {inputs gates : Nat} →
  WireRef inputs gates →
  Vec Bool inputs →
  Vec Bool gates →
  Bool
evaluateWire (inputWire index) inputValues gateValues =
  lookupVec index inputValues
evaluateWire (gateWire index) inputValues gateValues =
  lookupVec index gateValues

evaluateGate :
  ∀ {inputs gates : Nat} →
  Gate inputs gates →
  Vec Bool inputs →
  Vec Bool gates →
  Bool
evaluateGate (constantGate value) inputValues gateValues =
  value
evaluateGate (notGate source) inputValues gateValues =
  Cook.notBool
    (evaluateWire source inputValues gateValues)
evaluateGate (andGate left right) inputValues gateValues =
  Cook.andBool
    (evaluateWire left inputValues gateValues)
    (evaluateWire right inputValues gateValues)
evaluateGate (orGate left right) inputValues gateValues =
  Cook.orBool
    (evaluateWire left inputValues gateValues)
    (evaluateWire right inputValues gateValues)

evaluateProgram :
  ∀ {inputs gates : Nat} →
  GateProgram inputs gates →
  Vec Bool inputs →
  Vec Bool gates
evaluateProgram noGates inputValues =
  []
evaluateProgram (appendGate previous gate) inputValues =
  evaluateGate
    gate
    inputValues
    (evaluateProgram previous inputValues)
  ∷
  evaluateProgram previous inputValues

------------------------------------------------------------------------
-- A concrete circuit chooses one final output wire after all gates exist.
------------------------------------------------------------------------

record ConcreteBooleanCircuit (inputs : Nat) : Set₁ where
  constructor concrete-boolean-circuit
  field
    gateCount : Nat
    program : GateProgram inputs gateCount
    outputWire : WireRef inputs gateCount

open ConcreteBooleanCircuit public

evaluateCircuit :
  ∀ {inputs : Nat} →
  ConcreteBooleanCircuit inputs →
  Vec Bool inputs →
  Bool
evaluateCircuit circuit inputValues =
  evaluateWire
    (outputWire circuit)
    inputValues
    (evaluateProgram (program circuit) inputValues)

circuitSize :
  ∀ {inputs : Nat} →
  ConcreteBooleanCircuit inputs →
  Nat
circuitSize =
  gateCount

------------------------------------------------------------------------
-- Sanity witnesses: zero-gate circuits can only expose input wires.
------------------------------------------------------------------------

zeroGateInputCircuit :
  ∀ {inputs : Nat} →
  Fin inputs →
  ConcreteBooleanCircuit inputs
zeroGateInputCircuit index =
  concrete-boolean-circuit
    zero
    noGates
    (inputWire index)

zeroGateInputCircuitEvaluatesToInput :
  ∀ {inputs : Nat}
    (index : Fin inputs)
    (inputValues : Vec Bool inputs) →
  evaluateCircuit
    (zeroGateInputCircuit index)
    inputValues
  ≡ lookupVec index inputValues
zeroGateInputCircuitEvaluatesToInput index inputValues =
  refl

------------------------------------------------------------------------
-- One-gate examples.
------------------------------------------------------------------------

constantCircuit :
  ∀ {inputs : Nat} →
  Bool →
  ConcreteBooleanCircuit inputs
constantCircuit value =
  concrete-boolean-circuit
    (suc zero)
    (appendGate noGates (constantGate value))
    (gateWire fzero)

constantCircuitCorrect :
  ∀ {inputs : Nat}
    (value : Bool)
    (inputValues : Vec Bool inputs) →
  evaluateCircuit (constantCircuit value) inputValues
  ≡ value
constantCircuitCorrect value inputValues =
  refl

notInputCircuit :
  ∀ {inputs : Nat} →
  Fin inputs →
  ConcreteBooleanCircuit inputs
notInputCircuit index =
  concrete-boolean-circuit
    (suc zero)
    (appendGate noGates
      (notGate (inputWire index)))
    (gateWire fzero)

notInputCircuitCorrect :
  ∀ {inputs : Nat}
    (index : Fin inputs)
    (inputValues : Vec Bool inputs) →
  evaluateCircuit
    (notInputCircuit index)
    inputValues
  ≡ Cook.notBool (lookupVec index inputValues)
notInputCircuitCorrect index inputValues =
  refl

------------------------------------------------------------------------
-- Concrete family target.
--
-- This deliberately does not say "polynomial" yet.  A later family theorem
-- must attach an actual numeric gate-count envelope and prove its bound.
------------------------------------------------------------------------

record ConcreteCircuitFamily : Set₁ where
  field
    circuitAtWidth :
      (inputWidth : Nat) →
      ConcreteBooleanCircuit inputWidth

    gateCountEnvelope :
      Nat → Nat

    gateCountWithinEnvelope :
      (inputWidth : Nat) →
      circuitSize (circuitAtWidth inputWidth)
      ≡ gateCountEnvelope inputWidth

open ConcreteCircuitFamily public
