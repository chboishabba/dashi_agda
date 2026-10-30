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

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Fin.Base using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Vec.Base using (Vec; []; _∷_)
open import Data.Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (sym; cong; cong₂)

import DASHI.Mathematics.Complexity.PNotEqualsNPConcreteBooleanCircuitDAGExact as Circuit
import DASHI.Mathematics.Complexity.PNotEqualsNPConcreteCircuitSharedSemanticsExact as Existing
import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1TruthTableRepairGeneratorExact as VectorOwner

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

-- Reuse the existing P-vs-NP truth-table owner's pointwise finite-vector
-- extensionality. It supplies structural induction without an extensionality
-- postulate; no second Vec theorem is introduced here.

-- Conversely, decode+re-encode recovers ALL FINITE assignment values,
-- not merely existential satisfiability. Proof fields are not counted.
encodeDecodeAuxiliary :
  ∀ {inputs : Nat}
    (circuit : Circuit.ConcreteBooleanCircuit inputs)
    (model : FiniteSupportedModel circuit) →
  auxiliaryBits (encodeAccepted circuit (decodeSupported circuit model))
    ≡ auxiliaryBits model
encodeDecodeAuxiliary circuit model =
  VectorOwner.vecExtensionality
    (Circuit.evaluateProgram (Circuit.program circuit) (inputBits model))
    (auxiliaryBits model)
    (λ i → sym (auxiliaryCorrect model i))

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


------------------------------------------------------------------------
-- SAME-OBJECT BRIDGE: an accepted finite-support model is a model of the
-- ORIGINAL shared acceptance formula, and any original satisfying witness
-- yields the finite-support model. Both arrows call the 2026-09 #1040
-- semantic theorem; there is no new SAT solver or duplicated gate compiler.
------------------------------------------------------------------------

finiteSupportedGivesSharedSAT :
  ∀ {inputs : Nat}
    (circuit : Circuit.ConcreteBooleanCircuit inputs) →
  FiniteSupportedModel circuit →
  Cook.Satisfiable (Existing.sharedAcceptanceFormula circuit)
finiteSupportedGivesSharedSAT circuit model =
  Existing.acceptedInputGivesSharedSatisfiable
    circuit (inputBits model) (outputTrue model)

sharedSATGivesFiniteSupported :
  ∀ {inputs : Nat}
    (circuit : Circuit.ConcreteBooleanCircuit inputs) →
  Cook.Satisfiable (Existing.sharedAcceptanceFormula circuit) →
  FiniteSupportedModel circuit
sharedSATGivesFiniteSupported circuit witness
  with Existing.sharedSatisfiableGivesAcceptedInput circuit witness
... | bits , accepted =
  encodeAccepted circuit (bits , accepted)

-- Consequence: the specific existing shared SAT formula has precisely the
-- finite normal-form witness semantics above. Numerically counting all
-- unrestricted Cook.Assignment inhabitants would still overcount.


------------------------------------------------------------------------
-- EXACT NAT-VALUED FINITE #SAT: same carrier, no arbitrary Nat->Bool tail.
--
-- Every n-vector is counted exactly once by structural binary recursion.
-- The auxiliary test is the literal Boolean equality of the auxiliary
-- vector with evaluateProgram for the original concrete DAG.
-- The resulting equality is NUMERIC, not only an existential SAT bridge.
--
-- No new circuit/Tseitin compiler, no postulates, and no abstract
-- counting-engine axioms. Kernel checking remains outstanding.
------------------------------------------------------------------------

-- The per-vector weight belongs to the finite Boolean model count.
indicator : Bool → Nat
indicator true = suc zero
indicator false = zero

sumBoolVectors :
  ∀ {n : Nat} → (Vec Bool n → Nat) → Nat
sumBoolVectors {zero} weight = weight []
sumBoolVectors {suc n} weight =
  sumBoolVectors (λ tail → weight (false ∷ tail)) +
  sumBoolVectors (λ tail → weight (true ∷ tail))

sumBoolVectorsExt :
  ∀ {n : Nat} (weight₁ weight₂ : Vec Bool n → Nat) →
  ((bits : Vec Bool n) → weight₁ bits ≡ weight₂ bits) →
  sumBoolVectors weight₁ ≡ sumBoolVectors weight₂
sumBoolVectorsExt {zero} weight₁ weight₂ pointwise =
  pointwise []
sumBoolVectorsExt {suc n} weight₁ weight₂ pointwise =
  cong₂ _+_
    (sumBoolVectorsExt
      (λ tail → weight₁ (false ∷ tail))
      (λ tail → weight₂ (false ∷ tail))
      (λ tail → pointwise (false ∷ tail)))
    (sumBoolVectorsExt
      (λ tail → weight₁ (true ∷ tail))
      (λ tail → weight₂ (true ∷ tail))
      (λ tail → pointwise (true ∷ tail)))

sumBoolVectorsZero :
  ∀ {n : Nat} →
  sumBoolVectors {n} (λ _ → zero) ≡ zero
sumBoolVectorsZero {zero} = refl
sumBoolVectorsZero {suc n}
  rewrite sumBoolVectorsZero {n} = refl

-- Computable equality on the exact finite auxiliary data carrier.
equalBoolVectors : ∀ {n : Nat} → Vec Bool n → Vec Bool n → Bool
equalBoolVectors [] [] = true
equalBoolVectors (false ∷ xs) (false ∷ ys) =
  equalBoolVectors xs ys
equalBoolVectors (true ∷ xs) (true ∷ ys) =
  equalBoolVectors xs ys
equalBoolVectors (false ∷ xs) (true ∷ ys) = false
equalBoolVectors (true ∷ xs) (false ∷ ys) = false

-- Exhaustively searching a finite Boolean vector returns exactly ONE match
-- to a given vector, even when the vector is empty.
sumExactlyOneEqualVector :
  ∀ {n : Nat} (target : Vec Bool n) →
  sumBoolVectors (λ candidate →
    indicator (equalBoolVectors candidate target)) ≡ suc zero
sumExactlyOneEqualVector [] = refl
sumExactlyOneEqualVector {n = suc n} (false ∷ target)
  rewrite sumExactlyOneEqualVector target
        | sumBoolVectorsZero {n} = refl
sumExactlyOneEqualVector {n = suc n} (true ∷ target)
  rewrite sumBoolVectorsZero {n}
        | sumExactlyOneEqualVector target = refl

-- A rejected input has no matching *accepted* gate extension.
-- An accepted input has exactly one: the original DAG's evaluation.
acceptedAuxiliaryMatch :
  ∀ {n : Nat} →
  Bool → Vec Bool n → Vec Bool n → Bool
acceptedAuxiliaryMatch true target candidate =
  equalBoolVectors candidate target
acceptedAuxiliaryMatch false target candidate = false

countAcceptedAuxiliaries :
  ∀ {n : Nat} (accept : Bool) (target : Vec Bool n) →
  sumBoolVectors (λ candidate →
    indicator (acceptedAuxiliaryMatch accept target candidate))
  ≡ indicator accept
countAcceptedAuxiliaries true target =
  sumExactlyOneEqualVector target
countAcceptedAuxiliaries false target =
  sumBoolVectorsZero

-- Count accepting INPUT valuations of the already existing circuit.
-- This does not enumerate an infinite Cook.Assignment.
countAcceptedCircuitInputs :
  ∀ {inputs : Nat} → Circuit.ConcreteBooleanCircuit inputs → Nat
countAcceptedCircuitInputs circuit =
  sumBoolVectors (λ bits →
    indicator (Circuit.evaluateCircuit circuit bits))

-- Count satisfying pairs of INPUT and GATE vectors with every gate
-- constrained to the exact output of evaluateProgram. This is the
-- finite-support, count-preserving same-object Tseitin model count.
countFiniteSupportedTseitin :
  ∀ {inputs : Nat} → Circuit.ConcreteBooleanCircuit inputs → Nat
countFiniteSupportedTseitin circuit =
  sumBoolVectors (λ bits →
    sumBoolVectors (λ auxiliary →
      indicator
        (acceptedAuxiliaryMatch
          (Circuit.evaluateCircuit circuit bits)
          (Circuit.evaluateProgram (Circuit.program circuit) bits)
          auxiliary)))

-- THE NUMERIC CARDINALITY RESULT, for every concrete DAG, with no
-- complexity assumptions. Uses a single canonical extension per input.
-- This is NOT an OpenAI ETH runtime theorem, nor a bounded-width CNF theorem.
finiteSupportedTseitinCountExact :
  ∀ {inputs : Nat} (circuit : Circuit.ConcreteBooleanCircuit inputs) →
  countFiniteSupportedTseitin circuit
    ≡ countAcceptedCircuitInputs circuit
finiteSupportedTseitinCountExact circuit =
  sumBoolVectorsExt
    (λ bits →
      sumBoolVectors (λ auxiliary →
        indicator
          (acceptedAuxiliaryMatch
            (Circuit.evaluateCircuit circuit bits)
            (Circuit.evaluateProgram (Circuit.program circuit) bits)
            auxiliary)))
    (λ bits →
      indicator (Circuit.evaluateCircuit circuit bits))
    (λ bits →
      countAcceptedAuxiliaries
        (Circuit.evaluateCircuit circuit bits)
        (Circuit.evaluateProgram (Circuit.program circuit) bits))


------------------------------------------------------------------------
-- The executable counted predicate is the exact FINITE data predicate,
-- not a proxy. Equal vector bits imply equal literal auxiliary vectors.
------------------------------------------------------------------------

equalBoolVectorsSound :
  ∀ {n : Nat} (left right : Vec Bool n) →
  equalBoolVectors left right ≡ true → left ≡ right
equalBoolVectorsSound [] [] proof = refl
equalBoolVectorsSound (false ∷ xs) (false ∷ ys) proof =
  cong (λ rest → false ∷ rest)
    (equalBoolVectorsSound xs ys proof)
equalBoolVectorsSound (true ∷ xs) (true ∷ ys) proof =
  cong (λ rest → true ∷ rest)
    (equalBoolVectorsSound xs ys proof)
equalBoolVectorsSound (false ∷ xs) (true ∷ ys) ()
equalBoolVectorsSound (true ∷ xs) (false ∷ ys) ()

equalBoolVectorsRefl :
  ∀ {n : Nat} (bits : Vec Bool n) →
  equalBoolVectors bits bits ≡ true
equalBoolVectorsRefl [] = refl
equalBoolVectorsRefl (false ∷ rest) = equalBoolVectorsRefl rest
equalBoolVectorsRefl (true ∷ rest) = equalBoolVectorsRefl rest

-- Every already constructed finite-supported model passes the Boolean test
-- whose complete enumeration is used by countFiniteSupportedTseitin.
finiteSupportedModelIsCounted :
  ∀ {inputs : Nat}
    (circuit : Circuit.ConcreteBooleanCircuit inputs)
    (model : FiniteSupportedModel circuit) →
  acceptedAuxiliaryMatch
    (Circuit.evaluateCircuit circuit (inputBits model))
    (Circuit.evaluateProgram
      (Circuit.program circuit) (inputBits model))
    (auxiliaryBits model)
  ≡ true
finiteSupportedModelIsCounted circuit model
  rewrite outputTrue model
        | encodeDecodeAuxiliary circuit model =
  equalBoolVectorsRefl (auxiliaryBits model)

-- Conversely, an accepted *counted* Boolean pair supplies exactly the
-- original finite-supported model constructor, with the correct gate bits.
countedPairGivesFiniteSupportedModel :
  ∀ {inputs : Nat}
    (circuit : Circuit.ConcreteBooleanCircuit inputs)
    (bits : Vec Bool inputs)
    (auxiliary : Vec Bool (Circuit.gateCount circuit)) →
  acceptedAuxiliaryMatch
    (Circuit.evaluateCircuit circuit bits)
    (Circuit.evaluateProgram (Circuit.program circuit) bits)
    auxiliary
  ≡ true →
  FiniteSupportedModel circuit
countedPairGivesFiniteSupportedModel circuit bits auxiliary counted
  with Circuit.evaluateCircuit circuit bits
... | false with counted
...   | ()
... | true =
  finite-supported-model
    bits auxiliary
    (λ i →
      cong (Circuit.lookupVec i)
        (equalBoolVectorsSound auxiliary
          (Circuit.evaluateProgram (Circuit.program circuit) bits)
          counted))
    refl
