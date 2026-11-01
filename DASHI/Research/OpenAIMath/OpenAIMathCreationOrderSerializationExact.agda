module DASHI.Research.OpenAIMath.OpenAIMathCreationOrderSerializationExact where

------------------------------------------------------------------------
-- M00a: typed creation-order AST transport for the EXISTING original DAG.
--
-- Source owner: PNotEqualsNPConcreteBooleanCircuitDAGExact.agda (#1040).
-- Index theorem owner: OpenAIMathFiniteSupportedTseitinModelsExact.agda
--   chronologicalGateNumberExact (#1212).
-- Mathematical roots: Cook--Levin/Tseitin, finite index reversal.
--
-- The existing gateWire index 0 is newest-first. The Python ingress JSON
-- gate index 0 is creation-first. The latter is represented here by Fin g
-- rather than an unchecked Nat. This file DOES NOT define a second Boolean
-- evaluator/solver or claim an Agda theorem about JSON bytes/parser.
-- The latter (M00b and textual JSON injectivity) remains a proof obligation.
--
-- Source-written in PR #1212; exact-head Agda kernel acceptance PENDING.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Vec.Base using (Vec)
import Data.Fin.Base as Fin
import Data.Fin.Properties as FinP
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans)

import DASHI.Mathematics.Complexity.PNotEqualsNPConcreteBooleanCircuitDAGExact as Circuit
import DASHI.Mathematics.Complexity.PNotEqualsNPConcreteCircuitSharedCompilerExact as Compiler
import DASHI.Research.OpenAIMath.OpenAIMathFiniteSupportedTseitinModelsExact as Source
import DASHI.Research.OpenAIMath.OpenAIMathSharedTseitinOptimizedCNFExact as Opt

-- This carrier is the typed AST corresponding to the JSON wire's
-- "input" and "gate" constructors, not a permissive Nat index.
data CreationWire (inputs gates : Nat) : Set where
  creationInput : Fin.Fin inputs → CreationWire inputs gates
  creationGate : Fin.Fin gates → CreationWire inputs gates

encodeWire : ∀ {inputs gates : Nat} →
  Circuit.WireRef inputs gates → CreationWire inputs gates
encodeWire (Circuit.inputWire index) = creationInput index
encodeWire (Circuit.gateWire index) =
  creationGate (Fin.opposite index)

decodeWire : ∀ {inputs gates : Nat} →
  CreationWire inputs gates → Circuit.WireRef inputs gates
decodeWire (creationInput index) = Circuit.inputWire index
decodeWire (creationGate index) =
  Circuit.gateWire (Fin.opposite index)

decodeEncodeWire : ∀ {inputs gates : Nat}
  (wire : Circuit.WireRef inputs gates) →
  decodeWire (encodeWire wire) ≡ wire
decodeEncodeWire (Circuit.inputWire index) = refl
decodeEncodeWire (Circuit.gateWire index) =
  cong Circuit.gateWire (FinP.opposite-involutive index)

encodeDecodeWire : ∀ {inputs gates : Nat}
  (wire : CreationWire inputs gates) →
  encodeWire (decodeWire wire) ≡ wire
encodeDecodeWire (creationInput index) = refl
encodeDecodeWire (creationGate index) =
  cong creationGate (FinP.opposite-involutive index)

-- Constructor-specific, with the actual original gate operation order.
data CreationGate (inputs gates : Nat) : Set where
  creationConstant : Bool → CreationGate inputs gates
  creationNot : CreationWire inputs gates → CreationGate inputs gates
  creationAnd : CreationWire inputs gates → CreationWire inputs gates →
                CreationGate inputs gates
  creationOr : CreationWire inputs gates → CreationWire inputs gates →
               CreationGate inputs gates

encodeGate : ∀ {inputs gates : Nat} →
  Circuit.Gate inputs gates → CreationGate inputs gates
encodeGate (Circuit.constantGate value) = creationConstant value
encodeGate (Circuit.notGate source) = creationNot (encodeWire source)
encodeGate (Circuit.andGate left right) =
  creationAnd (encodeWire left) (encodeWire right)
encodeGate (Circuit.orGate left right) =
  creationOr (encodeWire left) (encodeWire right)

decodeGate : ∀ {inputs gates : Nat} →
  CreationGate inputs gates → Circuit.Gate inputs gates
decodeGate (creationConstant value) = Circuit.constantGate value
decodeGate (creationNot source) = Circuit.notGate (decodeWire source)
decodeGate (creationAnd left right) =
  Circuit.andGate (decodeWire left) (decodeWire right)
decodeGate (creationOr left right) =
  Circuit.orGate (decodeWire left) (decodeWire right)

decodeEncodeGate : ∀ {inputs gates : Nat}
  (gate : Circuit.Gate inputs gates) →
  decodeGate (encodeGate gate) ≡ gate
decodeEncodeGate (Circuit.constantGate value) = refl
decodeEncodeGate (Circuit.notGate source) =
  cong Circuit.notGate (decodeEncodeWire source)
decodeEncodeGate (Circuit.andGate left right) =
  cong₂ Circuit.andGate (decodeEncodeWire left) (decodeEncodeWire right)
decodeEncodeGate (Circuit.orGate left right) =
  cong₂ Circuit.orGate (decodeEncodeWire left) (decodeEncodeWire right)

encodeDecodeGate : ∀ {inputs gates : Nat}
  (gate : CreationGate inputs gates) →
  encodeGate (decodeGate gate) ≡ gate
encodeDecodeGate (creationConstant value) = refl
encodeDecodeGate (creationNot source) =
  cong creationNot (encodeDecodeWire source)
encodeDecodeGate (creationAnd left right) =
  cong₂ creationAnd (encodeDecodeWire left) (encodeDecodeWire right)
encodeDecodeGate (creationOr left right) =
  cong₂ creationOr (encodeDecodeWire left) (encodeDecodeWire right)

-- The recursive program still enforces acyclicity at construction depth.
data CreationProgram (inputs : Nat) : Nat → Set where
  creationEmpty : CreationProgram inputs zero
  creationAppend : ∀ {gates : Nat} →
    CreationProgram inputs gates → CreationGate inputs gates →
    CreationProgram inputs (suc gates)

encodeProgram : ∀ {inputs gates : Nat} →
  Circuit.GateProgram inputs gates → CreationProgram inputs gates
encodeProgram Circuit.noGates = creationEmpty
encodeProgram (Circuit.appendGate earlier gate) =
  creationAppend (encodeProgram earlier) (encodeGate gate)

decodeProgram : ∀ {inputs gates : Nat} →
  CreationProgram inputs gates → Circuit.GateProgram inputs gates
decodeProgram creationEmpty = Circuit.noGates
decodeProgram (creationAppend earlier gate) =
  Circuit.appendGate (decodeProgram earlier) (decodeGate gate)

decodeEncodeProgram : ∀ {inputs gates : Nat}
  (program : Circuit.GateProgram inputs gates) →
  decodeProgram (encodeProgram program) ≡ program
decodeEncodeProgram Circuit.noGates = refl
decodeEncodeProgram (Circuit.appendGate earlier gate) =
  cong₂ Circuit.appendGate
    (decodeEncodeProgram earlier) (decodeEncodeGate gate)

encodeDecodeProgram : ∀ {inputs gates : Nat}
  (program : CreationProgram inputs gates) →
  encodeProgram (decodeProgram program) ≡ program
encodeDecodeProgram creationEmpty = refl
encodeDecodeProgram (creationAppend earlier gate) =
  cong₂ creationAppend
    (encodeDecodeProgram earlier) (encodeDecodeGate gate)

-- Entire circuit, retaining the original gate-count and output-wire witness.
data CreationCircuit (inputs : Nat) : Set₁ where
  creationCircuit : (gates : Nat) →
    CreationProgram inputs gates → CreationWire inputs gates →
    CreationCircuit inputs

encodeCircuit : ∀ {inputs : Nat} →
  Circuit.ConcreteBooleanCircuit inputs → CreationCircuit inputs
encodeCircuit (Circuit.concrete-boolean-circuit gates program output) =
  creationCircuit gates (encodeProgram program) (encodeWire output)

decodeCircuit : ∀ {inputs : Nat} →
  CreationCircuit inputs → Circuit.ConcreteBooleanCircuit inputs
decodeCircuit (creationCircuit gates program output) =
  Circuit.concrete-boolean-circuit gates
    (decodeProgram program) (decodeWire output)

decodeEncodeCircuit : ∀ {inputs : Nat}
  (circuit : Circuit.ConcreteBooleanCircuit inputs) →
  decodeCircuit (encodeCircuit circuit) ≡ circuit
decodeEncodeCircuit (Circuit.concrete-boolean-circuit gates program output) =
  cong₂ (Circuit.concrete-boolean-circuit gates)
    (decodeEncodeProgram program) (decodeEncodeWire output)

encodeDecodeCircuit : ∀ {inputs : Nat}
  (circuit : CreationCircuit inputs) →
  encodeCircuit (decodeCircuit circuit) ≡ circuit
encodeDecodeCircuit (creationCircuit gates program output) =
  cong₂ (creationCircuit gates)
    (encodeDecodeProgram program) (encodeDecodeWire output)

-- Same variable coordinate, not just an isomorphic graph or model count.
creationWireVariable : ∀ {inputs gates : Nat} →
  CreationWire inputs gates → Nat
creationWireVariable (creationInput index) = Fin.toℕ index
creationWireVariable {inputs} (creationGate index) =
  inputs + Fin.toℕ index

originalWireVariable : ∀ {inputs gates : Nat} →
  Circuit.WireRef inputs gates → Nat
originalWireVariable (Circuit.inputWire index) = Fin.toℕ index
originalWireVariable {inputs} (Circuit.gateWire index) =
  Compiler.gateVariableIndex inputs index

creationWireVariableExact : ∀ {inputs gates : Nat}
  (wire : CreationWire inputs gates) →
  originalWireVariable (decodeWire wire) ≡ creationWireVariable wire
creationWireVariableExact (creationInput index) = refl
creationWireVariableExact {inputs} (creationGate index) =
  Source.chronologicalGateNumberExact inputs index

-- Preserve the ORIGINAL evaluator by an equality of original circuits,
-- not by constructing another evaluator for creation-order syntax.
creationCircuitEvaluationExact : ∀ {inputs : Nat}
  (circuit : Circuit.ConcreteBooleanCircuit inputs)
  (bits : Vec Bool inputs) →
  Circuit.evaluateCircuit (decodeCircuit (encodeCircuit circuit)) bits ≡
  Circuit.evaluateCircuit circuit bits
creationCircuitEvaluationExact circuit bits =
  cong (λ c → Circuit.evaluateCircuit c bits)
    (decodeEncodeCircuit circuit)

-- Reuse the earlier original finite-count owner. This is a statement
-- about that SAME Nat-valued accepted-input counting function.
creationCircuitAcceptedCountExact : ∀ {inputs : Nat}
  (circuit : Circuit.ConcreteBooleanCircuit inputs) →
  Source.countAcceptedCircuitInputs (decodeCircuit (encodeCircuit circuit)) ≡
  Source.countAcceptedCircuitInputs circuit
creationCircuitAcceptedCountExact circuit =
  cong Source.countAcceptedCircuitInputs (decodeEncodeCircuit circuit)

-- Composition with the SAME original Golden P2 theorem. These are
-- original typed source counts, not OAI machine output counts.
creationOriginalCompiledCountExact : ∀ {inputs : Nat}
  (circuit : Circuit.ConcreteBooleanCircuit inputs) →
  Source.originalCompiledCNFModelCount (decodeCircuit (encodeCircuit circuit))
    ≡ Source.originalCompiledCNFModelCount circuit
creationOriginalCompiledCountExact circuit =
  cong Source.originalCompiledCNFModelCount (decodeEncodeCircuit circuit)

creationOriginalTseitinCountExact : ∀ {inputs : Nat}
  (circuit : Circuit.ConcreteBooleanCircuit inputs) →
  Source.originalCompiledCNFModelCount (decodeCircuit (encodeCircuit circuit))
    ≡ Source.countAcceptedCircuitInputs circuit
creationOriginalTseitinCountExact circuit =
  trans (creationOriginalCompiledCountExact circuit)
    (Source.originalGlobalCNFCountExact circuit)

-- Same source numerical bridge using the EXISTING optional three-clause
-- owner. This carries the actual original optimized compiler, not a new
-- truth-table or SAT implementation.
creationOptimizedTseitinCountExact : ∀ {inputs : Nat}
  (circuit : Circuit.ConcreteBooleanCircuit inputs) →
  Opt.countSourceCNF
    (Opt.optCircuitCNF (decodeCircuit (encodeCircuit circuit)))
    ≡ Source.countAcceptedCircuitInputs circuit
creationOptimizedTseitinCountExact circuit =
  trans
    (cong (λ source → Opt.countSourceCNF (Opt.optCircuitCNF source))
      (decodeEncodeCircuit circuit))
    (Opt.optGlobalCNFCountExact circuit)

-- OPEN: prove the concrete JSON *bytes* parser recognizes precisely the
-- finite-indexed creation AST above, and that its emitted clauses and bits
-- coincide with optCircuitCNF and OpenAI Encoding.encodeCNF respectively.
-- The real compiler and fixed primitive machine cost joins remain M01-M05.
