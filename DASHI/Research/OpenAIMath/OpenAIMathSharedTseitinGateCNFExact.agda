module DASHI.Research.OpenAIMath.OpenAIMathSharedTseitinGateCNFExact where

------------------------------------------------------------------------
-- SAME-OBJECT, FIXED WIDTH ONLY: concrete DAG gate -> existing CNF compiler
--
-- The gate and evaluation are the existing P-vs-NP ConcreteBooleanCircuitDAG
-- owner (#1040). The CNF compiler/proofs are the existing Cook--Levin
-- FixedWidthTruthTableCNFExact owner. No new SAT compiler is defined.
--
-- A local gate uses only THREE truth bits: output, left input, right input.
-- Constants ignore both inputs; NOT ignores the right input. Full circuit
-- semantics need the original CNFVariableRenamingExact and
-- CNFPlacedConstraintConjunctionExact global placement owners. This module
-- proves the reusable *local* source gate truth/CNF bridge only.
--
-- Historical attribution: Cook--Levin, Tseitin and classical Boolean CNF.
-- New DASHI authoring is the exact finite source-to-source specialization.
-- Agda kernel acceptance remains pending. Never infer OpenAI 378 machine
-- complexity or Max-Cut 102 approximation-hardness from a local gate.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Vec.Base using (Vec)
import Data.Fin.Base as Fin

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PNotEqualsNPConcreteBooleanCircuitDAGExact as Circuit
import DASHI.Mathematics.Complexity.FixedWidthTruthTableCNFExact as CNF

three : Nat
three = suc (suc (suc zero))

GateWindow : Set
GateWindow = CNF.Bits three

window : Bool → Bool → Bool → GateWindow
window output left right =
  output CNF.∷ᵇ left CNF.∷ᵇ right CNF.∷ᵇ CNF.[]ᵇ

eqBool : Bool → Bool → Bool
eqBool false false = true
eqBool false true = false
eqBool true false = false
eqBool true true = true

eqBoolRefl : (value : Bool) → eqBool value value ≡ true
eqBoolRefl false = refl
eqBoolRefl true = refl

-- The Boolean gate relation uses the ORIGINAL gate constructors.
-- Repeated left/right wires are supported: no distinct-variable assumption.
localGateConsistent :
  ∀ {inputs gates : Nat} → Circuit.Gate inputs gates →
  GateWindow → Bool
localGateConsistent (Circuit.constantGate value) bits =
  eqBool (CNF.lookupBit bits Fin.zero) value
localGateConsistent (Circuit.notGate source) bits =
  eqBool
    (CNF.lookupBit bits Fin.zero)
    (Cook.notBool (CNF.lookupBit bits (Fin.suc Fin.zero)))
localGateConsistent (Circuit.andGate left right) bits =
  eqBool
    (CNF.lookupBit bits Fin.zero)
    (Cook.andBool
      (CNF.lookupBit bits (Fin.suc Fin.zero))
      (CNF.lookupBit bits (Fin.suc (Fin.suc Fin.zero))))
localGateConsistent (Circuit.orGate left right) bits =
  eqBool
    (CNF.lookupBit bits Fin.zero)
    (Cook.orBool
      (CNF.lookupBit bits (Fin.suc Fin.zero))
      (CNF.lookupBit bits (Fin.suc (Fin.suc Fin.zero))))

localLeft :
  ∀ {inputs gates : Nat} →
  Circuit.Gate inputs gates → Vec Bool inputs → Vec Bool gates → Bool
localLeft (Circuit.constantGate value) inputValues gateValues = false
localLeft (Circuit.notGate source) inputValues gateValues =
  Circuit.evaluateWire source inputValues gateValues
localLeft (Circuit.andGate left right) inputValues gateValues =
  Circuit.evaluateWire left inputValues gateValues
localLeft (Circuit.orGate left right) inputValues gateValues =
  Circuit.evaluateWire left inputValues gateValues

localRight :
  ∀ {inputs gates : Nat} →
  Circuit.Gate inputs gates → Vec Bool inputs → Vec Bool gates → Bool
localRight (Circuit.constantGate value) inputValues gateValues = false
localRight (Circuit.notGate source) inputValues gateValues = false
localRight (Circuit.andGate left right) inputValues gateValues =
  Circuit.evaluateWire right inputValues gateValues
localRight (Circuit.orGate left right) inputValues gateValues =
  Circuit.evaluateWire right inputValues gateValues

actualGateWindow :
  ∀ {inputs gates : Nat} →
  Circuit.Gate inputs gates → Vec Bool inputs → Vec Bool gates →
  GateWindow
actualGateWindow gate inputs previous =
  window
    (Circuit.evaluateGate gate inputs previous)
    (localLeft gate inputs previous)
    (localRight gate inputs previous)

-- The concrete source gate always satisfies its corresponding local
-- three-bit relation, including constant and repeated-wire cases.
actualGateConsistent :
  ∀ {inputs gates : Nat}
    (gate : Circuit.Gate inputs gates)
    (values : Vec Bool inputs)
    (previous : Vec Bool gates) →
  localGateConsistent gate (actualGateWindow gate values previous)
    ≡ true
actualGateConsistent (Circuit.constantGate value) values previous =
  eqBoolRefl value
actualGateConsistent (Circuit.notGate source) values previous =
  eqBoolRefl (Cook.notBool
    (Circuit.evaluateWire source values previous))
actualGateConsistent (Circuit.andGate left right) values previous =
  eqBoolRefl
    (Cook.andBool
      (Circuit.evaluateWire left values previous)
      (Circuit.evaluateWire right values previous))
actualGateConsistent (Circuit.orGate left right) values previous =
  eqBoolRefl
    (Cook.orBool
      (Circuit.evaluateWire left values previous)
      (Circuit.evaluateWire right values previous))

-- Reuse the ORIGINAL fixed-width truth-table CNF constructor. Since its
-- input window is always three bits, the exhaustive eight-row template is
-- constant-size. No exponential-width circuit expansion is performed here.
localGateCNF :
  ∀ {inputs gates : Nat} →
  Circuit.Gate inputs gates → CNF.CNF three
localGateCNF gate =
  CNF.truthTableCNF (localGateConsistent gate)

localGateCNFSound :
  ∀ {inputs gates : Nat}
    (gate : Circuit.Gate inputs gates)
    (bits : GateWindow) →
  CNF.evaluateCNF (localGateCNF gate) bits ≡ true →
  localGateConsistent gate bits ≡ true
localGateCNFSound gate bits =
  CNF.truthTableCNFSound (localGateConsistent gate) bits

localGateCNFComplete :
  ∀ {inputs gates : Nat}
    (gate : Circuit.Gate inputs gates)
    (bits : GateWindow) →
  localGateConsistent gate bits ≡ true →
  CNF.evaluateCNF (localGateCNF gate) bits ≡ true
localGateCNFComplete gate bits =
  CNF.truthTableCNFComplete (localGateConsistent gate) bits

actualGateCNFAccepts :
  ∀ {inputs gates : Nat}
    (gate : Circuit.Gate inputs gates)
    (values : Vec Bool inputs)
    (previous : Vec Bool gates) →
  CNF.evaluateCNF
    (localGateCNF gate)
    (actualGateWindow gate values previous)
  ≡ true
actualGateCNFAccepts gate values previous =
  localGateCNFComplete gate
    (actualGateWindow gate values previous)
    (actualGateConsistent gate values previous)
