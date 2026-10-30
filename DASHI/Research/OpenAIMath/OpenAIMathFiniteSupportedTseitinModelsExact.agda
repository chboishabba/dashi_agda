{-# OPTIONS --safe #-}
module DASHI.Research.OpenAIMath.OpenAIMathFiniteSupportedTseitinModelsExact where

------------------------------------------------------------------------
-- A finite, countable-support receiver for the existing shared/Tseitin
-- compiler, WITHOUT replacing the original circuit or gate semantics.
--
-- Source proof owners: DASHI/Mathematics/Complexity/
-- PNotEqualsNPConcreteBooleanCircuitDAGExact.agda and
-- PNotEqualsNPConcreteCircuitSharedSemanticsExact.agda (Agda PR #1040).
--
-- Existing prior owner #1212 establishes unique used-variable values for
-- arbitrary Cook.Assignment = Nat -> Bool. This module instead gives a
-- FINITE input/auxiliary model carrier and an exact round trip on its data.
-- This explicitly prevents the infinite unconstrained-tail overcount.
--
-- Original math attribution: Cook--Levin/Tseitin; new contribution is
-- a typed reuse of the existing concrete DASHI proof carriers.
-- Source-written; Agda kernel and finite-cardinality theorem pending.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Fin.Base using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Vec.Base using (Vec; []; _∷_)
open import Data.Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (sym)

import DASHI.Mathematics.Complexity.PNotEqualsNPConcreteBooleanCircuitDAGExact as Circuit

-- A model has precisely n+g bits, not an unrestricted Nat -> Bool tail.
-- Each auxiliary gate bit is REQUIRED to equal concrete DAG evaluation.
record FiniteSupportedModel
    {inputs : Nat}
    (circuit : Circuit.ConcreteBooleanCircuit inputs) : Set where
  constructor finite-supported-model
  field
    inputBits : Vec Bool inputs
    auxiliaryBits : Vec Bool (Circuit.gateCount circuit)
    auxiliaryCorrect : (i : Fin (Circuit.gateCount circuit)) →
      Circuit.lookupVec i auxiliaryBits ≡
      Circuit.lookupVec i
        (Circuit.evaluateProgram (Circuit.program circuit) inputBits)
    outputTrue : Circuit.evaluateCircuit circuit inputBits ≡ true

open FiniteSupportedModel public

AcceptedInputs :
  ∀ {inputs : Nat} (circuit : Circuit.ConcreteBooleanCircuit inputs) →
  Set
AcceptedInputs {inputs} circuit =
  Σ (Vec Bool inputs) (λ bits → Circuit.evaluateCircuit circuit bits ≡ true)

-- This finite support has a canonical, uniquely determined gate vector.
encodeAccepted :
  ∀ {inputs : Nat} (circuit : Circuit.ConcreteBooleanCircuit inputs) →
  AcceptedInputs circuit → FiniteSupportedModel circuit
encodeAccepted circuit (bits , accepted) =
  finite-supported-model bits
    (Circuit.evaluateProgram (Circuit.program circuit) bits)
    (λ i → refl)
    accepted

decodeSupported :
  ∀ {inputs : Nat} (circuit : Circuit.ConcreteBooleanCircuit inputs) →
  FiniteSupportedModel circuit → AcceptedInputs circuit
decodeSupported circuit model =
  inputBits model , outputTrue model

-- Exact round-trip, including the original acceptance certificate.
decodeEncodeAccepted :
  ∀ {inputs : Nat}
    (circuit : Circuit.ConcreteBooleanCircuit inputs)
    (accepted : AcceptedInputs circuit) →
  decodeSupported circuit (encodeAccepted circuit accepted) ≡ accepted
decodeEncodeAccepted circuit (bits , accepted) = refl

-- Finite vectors are determined by every indexed coordinate; no function
-- extensionality postulate or global Nat -> Bool assignment equality.
vecExt :
  ∀ {n : Nat} {left right : Vec Bool n} →
  ((i : Fin n) →
    Circuit.lookupVec i left ≡ Circuit.lookupVec i right) →
  left ≡ right
vecExt {zero} {[]} {[]} equal = refl
vecExt {suc n} {x ∷ xs} {y ∷ ys} equal
  rewrite equal fzero
        | vecExt {left = xs} {right = ys} (λ i → equal (fsuc i)) =
  refl

-- Conversely, decode+re-encode recovers ALL FINITE assignment values,
-- not merely existential satisfiability. Proof fields are not counted.
encodeDecodeAuxiliary :
  ∀ {inputs : Nat}
    (circuit : Circuit.ConcreteBooleanCircuit inputs)
    (model : FiniteSupportedModel circuit) →
  auxiliaryBits (encodeAccepted circuit (decodeSupported circuit model))
    ≡ auxiliaryBits model
encodeDecodeAuxiliary circuit model =
  vecExt (λ i → sym (auxiliaryCorrect model i))

encodeDecodeInput :
  ∀ {inputs : Nat}
    (circuit : Circuit.ConcreteBooleanCircuit inputs)
    (model : FiniteSupportedModel circuit) →
  inputBits (encodeAccepted circuit (decodeSupported circuit model))
    ≡ inputBits model
encodeDecodeInput circuit model = refl

-- Remaining: a chosen finite enumeration/cardinality library theorem to
-- translate this data-level isomorphism into Nat-valued #SAT counts; an
-- explicit parsimonious width-three CNF encoding and canonical bit lengths;
-- then machine-level bounds. No counting equality or speedup is asserted
-- without those concrete receipts.
