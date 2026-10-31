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
import Data.Fin.Base as FinBase
import Data.Fin.Properties as FinP
import Data.Nat.Properties as NatP
open import Data.Vec.Base using (Vec; []; _∷_)
open import Data.Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (sym; trans; cong; cong₂)

import DASHI.Mathematics.Complexity.PNotEqualsNPConcreteBooleanCircuitDAGExact as Circuit
import DASHI.Mathematics.Complexity.PNotEqualsNPConcreteCircuitSharedSemanticsExact as Existing
import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.FixedWidthTruthTableCNFExact as CNF
import DASHI.Mathematics.Complexity.ConcreteTapeCanonicalCellBitsExact as Canonical
import DASHI.Mathematics.Complexity.ConcreteTapeCanonicalWindowPlacementExact as Placement
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalBlockSliceConsistencyExact as Slice
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1TruthTableRepairGeneratorExact as VectorOwner
import DASHI.Research.OpenAIMath.OpenAIMathSharedTseitinGateCNFExact as Original
import DASHI.Mathematics.Complexity.PNotEqualsNPConcreteCircuitSharedCompilerExact as Compiler
import DASHI.Mathematics.Complexity.CNFVariableRenamingExact as Rename

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


------------------------------------------------------------------------
-- SAME-CARRIER BIT/VEC REIFICATION: actual source DAG finite Boolean
-- vectors and the older Cook-Levin CNF.Bits have the same finite data.
-- Search found older bitsExt/takeBits/block slice owners but no direct codec;
-- this is the minimal adapter needed before gate-value induction.
------------------------------------------------------------------------

bitsToFiniteVec : ∀ {n : Nat} → CNF.Bits n → Vec Bool n
bitsToFiniteVec CNF.[]ᵇ = []
bitsToFiniteVec (bit CNF.∷ᵇ rest) = bit ∷ bitsToFiniteVec rest

finiteVecToBits : ∀ {n : Nat} → Vec Bool n → CNF.Bits n
finiteVecToBits [] = CNF.[]ᵇ
finiteVecToBits (bit ∷ rest) = bit CNF.∷ᵇ finiteVecToBits rest

bitsVecRoundTrip : ∀ {n : Nat} (bits : CNF.Bits n) →
  finiteVecToBits (bitsToFiniteVec bits) ≡ bits
bitsVecRoundTrip CNF.[]ᵇ = refl
bitsVecRoundTrip (bit CNF.∷ᵇ rest) =
  cong (λ tail → bit CNF.∷ᵇ tail) (bitsVecRoundTrip rest)

vecBitsRoundTrip : ∀ {n : Nat} (bits : Vec Bool n) →
  bitsToFiniteVec (finiteVecToBits bits) ≡ bits
vecBitsRoundTrip [] = refl
vecBitsRoundTrip (bit ∷ rest) =
  cong (λ tail → bit ∷ tail) (vecBitsRoundTrip rest)

lookupCNFToVec : ∀ {n : Nat}
  (bits : CNF.Bits n) (index : Fin n) →
  CNF.lookupBit bits index ≡
    Circuit.lookupVec index (bitsToFiniteVec bits)
lookupCNFToVec (bit CNF.∷ᵇ rest) fzero = refl
lookupCNFToVec (bit CNF.∷ᵇ rest) (fsuc index) =
  lookupCNFToVec rest index

-- Data reification only: constructing the gate vector in creation order,
-- reifying every original numbered gate variable, and proving the whole
-- circuit CNF count equals accepted input count remain separate obligations.
-- No postulates, infinite tail assignment, or duplicate CNF datatype.


------------------------------------------------------------------------
-- REUSE original Cook-Levin GLOBAL BLOCK SLICE as the input-vector owner.
-- This pays the input-wire half of original-circuit CNF reification, rather
-- than proving a new Fin addition/left-injection lemma.
------------------------------------------------------------------------

inputVectorFromGlobal : ∀ {inputs gates : Nat} →
  CNF.Bits (inputs + gates) → Vec Bool inputs
inputVectorFromGlobal {inputs} bits =
  bitsToFiniteVec (Canonical.takeBits inputs bits)

inputVectorLookupExact : ∀ {inputs gates : Nat}
  (bits : CNF.Bits (inputs + gates))
  (index : Fin inputs) →
  Circuit.lookupVec index (inputVectorFromGlobal bits) ≡
    CNF.lookupBit bits (Placement.finLeft index)
inputVectorLookupExact {inputs} bits index =
  trans
    (sym (lookupCNFToVec (Canonical.takeBits inputs bits) index))
    (Slice.lookupTakeBits bits index)

-- Original producer/owner attribution: source finite DAG input indexing,
-- ConcreteTapeCanonicalCellBitsExact.takeBits,
-- ConcreteTapeCanonicalWindowPlacementExact.finLeft,
-- ConcreteTapeGlobalBlockSliceConsistencyExact.lookupTakeBits.
-- Remaining step is recursive newest-first GATE vector construction and
-- exact gate-value lookup at Compiler.gateVariableIndex; kernel pending.


------------------------------------------------------------------------
-- FULL FINITE-CARRIER REASSEMBLY at inputs+gates, reusing the old tape
-- take/append/drop proofs. The gate suffix is in chronological global
-- variable order; original GateProgram's evaluateProgram is newest-first,
-- so reordering/semantic gate induction is STILL an explicit next lemma.
------------------------------------------------------------------------

gateVectorFromGlobal : ∀ {inputs gates : Nat} →
  CNF.Bits (inputs + gates) → Vec Bool gates
gateVectorFromGlobal {inputs} bits =
  bitsToFiniteVec (Canonical.dropBits inputs bits)

globalBitsFromFiniteVectors : ∀ {inputs gates : Nat} →
  Vec Bool inputs → Vec Bool gates → CNF.Bits (inputs + gates)
globalBitsFromFiniteVectors inputValues gateValues =
  Canonical.appendBits
    (finiteVecToBits inputValues)
    (finiteVecToBits gateValues)

inputVectorSplitRoundTrip : ∀ {inputs gates : Nat}
  (inputValues : Vec Bool inputs)
  (gateValues : Vec Bool gates) →
  inputVectorFromGlobal
    (globalBitsFromFiniteVectors inputValues gateValues)
    ≡ inputValues
inputVectorSplitRoundTrip inputValues gateValues =
  trans
    (cong bitsToFiniteVec
      (Canonical.takeAppendBits
        (finiteVecToBits inputValues) (finiteVecToBits gateValues)))
    (vecBitsRoundTrip inputValues)

gateVectorSplitRoundTrip : ∀ {inputs gates : Nat}
  (inputValues : Vec Bool inputs)
  (gateValues : Vec Bool gates) →
  gateVectorFromGlobal
    (globalBitsFromFiniteVectors inputValues gateValues)
    ≡ gateValues
gateVectorSplitRoundTrip inputValues gateValues =
  trans
    (cong bitsToFiniteVec
      (Canonical.dropAppendBits
        (finiteVecToBits inputValues) (finiteVecToBits gateValues)))
    (vecBitsRoundTrip gateValues)

reassembleTakeDrop : ∀ {inputs gates : Nat}
  (bits : CNF.Bits (inputs + gates)) →
  Canonical.appendBits
    (Canonical.takeBits inputs bits)
    (Canonical.dropBits inputs bits) ≡ bits
reassembleTakeDrop {zero} bits = refl
reassembleTakeDrop {suc inputs} (bit CNF.∷ᵇ rest) =
  cong (λ tail → bit CNF.∷ᵇ tail) (reassembleTakeDrop rest)

globalFiniteVectorsRoundTrip : ∀ {inputs gates : Nat}
  (bits : CNF.Bits (inputs + gates)) →
  globalBitsFromFiniteVectors
    (inputVectorFromGlobal bits)
    (gateVectorFromGlobal bits)
    ≡ bits
globalFiniteVectorsRoundTrip {inputs} bits =
  trans
    (cong₂ Canonical.appendBits
      (bitsVecRoundTrip (Canonical.takeBits inputs bits))
      (bitsVecRoundTrip (Canonical.dropBits inputs bits)))
    (reassembleTakeDrop bits)

-- This pays the whole global finite-data isomorphism, not the original
-- circuit gate evaluator relation or global #SAT of accepted input vectors.
-- The original gate's newest-first vs global chronological order is retained
-- as a checked, explicitly unpaid semantic bridge. Agda kernel pending.


------------------------------------------------------------------------
-- FINITE CNF.Bits -> ORIGINAL Cook.Assignment ADAPTER (no second SAT logic)
--
-- Cook.Assignment = Nat -> Bool is total. The finite compiled circuit uses
-- only indices < n; all indices outside that fixed support get arbitrary
-- false. This is NOT uniqueness of the entire Nat -> Bool tail.
------------------------------------------------------------------------

finiteCNFToCookAssignment : ∀ {n : Nat} →
  CNF.Bits n → Cook.Assignment
finiteCNFToCookAssignment CNF.[]ᵇ index = false
finiteCNFToCookAssignment (bit CNF.∷ᵇ rest) zero = bit
finiteCNFToCookAssignment (bit CNF.∷ᵇ rest) (suc index) =
  finiteCNFToCookAssignment rest index

finiteCNFToCookLookup : ∀ {n : Nat}
  (bits : CNF.Bits n) (index : Fin n) →
  finiteCNFToCookAssignment bits (FinBase.toℕ index)
    ≡ CNF.lookupBit bits index
finiteCNFToCookLookup (bit CNF.∷ᵇ rest) fzero = refl
finiteCNFToCookLookup (bit CNF.∷ᵇ rest) (fsuc index) =
  finiteCNFToCookLookup rest index

-- The input-value extractor is EXACTLY the one already used by the
-- concrete-DAG source proof: it reads the first inputs bits from the
-- original finite CNF assignment, not a new model ontology.
finiteCNFCookInputExact : ∀ {inputs gates : Nat}
  (bits : CNF.Bits (inputs + gates))
  (index : Fin inputs) →
  finiteCNFToCookAssignment bits
    (FinBase.toℕ (Placement.finLeft index))
    ≡ Circuit.lookupVec index (inputVectorFromGlobal bits)
finiteCNFCookInputExact bits index =
  trans
    (finiteCNFToCookLookup bits (Placement.finLeft index))
    (sym (inputVectorLookupExact bits index))

-- A proof-friendly form of the same gate-variable identity, without
-- introducing a second numbered-gate compiler.
finiteCNFCookGateIndexExact : ∀ {inputs gates : Nat}
  (bits : CNF.Bits (inputs + gates))
  (index : Fin (inputs + gates)) →
  finiteCNFToCookAssignment bits (FinBase.toℕ index)
    ≡ CNF.lookupBit bits index
finiteCNFCookGateIndexExact = finiteCNFToCookLookup

-- Next outstanding *same-object* bridge: prove that the placed original
-- gate constraints in ProgramPlacedGatesValid imply the original
-- Compiler.programSharedConstraints under this finite adapter, then
-- directly reuse Existing.sharedConstraintsGiveRealization for the
-- chronological vs newest-first evaluation, and the already-authored
-- numeric finite-source-#SAT theorem.
-- SOURCE-WRITTEN; no Agda kernel check in this environment.


------------------------------------------------------------------------
-- EXACT ORIGINAL-COMPILER NUMERIC GATE/INPUT-WIRE PROVENANCE.
-- Prior and newest gate variables reuse the SOURCE compiler indices,
-- rather than an invented assignment numbering scheme.
------------------------------------------------------------------------

finiteCNFCookPriorWireExact : ∀ {inputs gates : Nat}
  (source : Circuit.WireRef inputs gates)
  (bits : CNF.Bits (inputs + suc gates)) →
  finiteCNFToCookAssignment bits (Original.wireNumber source)
    ≡ CNF.lookupBit bits (Original.wireFin source)
finiteCNFCookPriorWireExact source bits =
  trans
    (cong (finiteCNFToCookAssignment bits)
      (sym (FinP.toℕ-fromℕ< (Original.wireNumberBelow source))))
    (finiteCNFToCookLookup bits (Original.wireFin source))

finiteCNFCookNewestGateExact : ∀ {inputs gates : Nat}
  (gate : Circuit.Gate inputs gates)
  (bits : CNF.Bits (inputs + suc gates)) →
  finiteCNFToCookAssignment bits (inputs + gates)
    ≡ CNF.lookupBit bits
      (Original.gateWindowRename gate FinBase.zero)
finiteCNFCookNewestGateExact gate bits =
  trans
    (cong (finiteCNFToCookAssignment bits)
      (sym (Original.gateOutputIndexExact gate)))
    (finiteCNFToCookLookup bits
      (Original.gateWindowRename gate FinBase.zero))

-- Together with Existing.gateExpressionCorrect and
-- Original.compiledProgramLastGateOutputForced, these are the literal
-- left/right numerical joins for the existing ORIGINAL
-- ProgramAssignmentRealizes semantic induction. It remains necessary
-- to prove that the older finite assignment prefix agrees with the
-- original entire Cook assignment on all previously used coordinates.
-- No global #SAT promotion until that statement is paid.


------------------------------------------------------------------------
-- REUSE the original #1040 ProgramAssignmentRealizes invariant to pay
-- actual gate semantics. The placed CNF has the SAME numeric variables.
------------------------------------------------------------------------

finiteCNFCookWireValueFromRealization :
  ∀ {inputs gates : Nat}
    {previous : Circuit.GateProgram inputs gates}
    (bits : CNF.Bits (inputs + suc gates))
    (prior : Existing.ProgramAssignmentRealizes previous
      (finiteCNFToCookAssignment bits))
    (source : Circuit.WireRef inputs gates) →
  CNF.lookupBit bits (Original.wireFin source)
    ≡ Circuit.evaluateWire source
      (Existing.inputValues prior)
      (Circuit.evaluateProgram previous (Existing.inputValues prior))
finiteCNFCookWireValueFromRealization bits prior source =
  trans
    (sym (finiteCNFCookPriorWireExact source bits))
    (Existing.wireFormulaCorrect prior source)

-- The finite global CNF's operands have exactly the original source
-- wire values when the previous program's semantics are realized.
finiteCNFWindowWireValue :
  ∀ {inputs gates : Nat}
    {previous : Circuit.GateProgram inputs gates}
    (gate : Circuit.Gate inputs gates)
    (bits : CNF.Bits (inputs + suc gates))
    (prior : Existing.ProgramAssignmentRealizes previous
      (finiteCNFToCookAssignment bits))
    (source : Circuit.WireRef inputs gates)
    (index : Fin Original.three)
    (sourceAtIndex :
      Original.gateWindowRename gate index ≡ Original.wireFin source) →
  CNF.lookupBit
      (Rename.pullbackBits (Original.gateWindowRename gate) bits)
      index
    ≡ Circuit.evaluateWire source
      (Existing.inputValues prior)
      (Circuit.evaluateProgram previous (Existing.inputValues prior))
finiteCNFWindowWireValue gate bits prior source index sourceAtIndex =
  trans
    (Rename.pullbackLookup
      (Original.gateWindowRename gate) bits index)
    (trans
      (cong (CNF.lookupBit bits) sourceAtIndex)
      (finiteCNFCookWireValueFromRealization bits prior source))

-- This is the exact structural gate-induction *step* on an existing
-- realization: new finite-CNF fresh output must equal original evaluateGate.
finiteCNFPlacedGateOriginalStep :
  ∀ {inputs gates : Nat}
    {previous : Circuit.GateProgram inputs gates}
    (gate : Circuit.Gate inputs gates)
    (bits : CNF.Bits (inputs + suc gates))
    (prior : Existing.ProgramAssignmentRealizes previous
      (finiteCNFToCookAssignment bits)) →
  Original.localGateConsistent gate
    (Rename.pullbackBits (Original.gateWindowRename gate) bits) ≡ true →
  finiteCNFToCookAssignment bits (inputs + gates)
    ≡ Circuit.evaluateGate gate
      (Existing.inputValues prior)
      (Circuit.evaluateProgram previous (Existing.inputValues prior))
finiteCNFPlacedGateOriginalStep (Circuit.constantGate value) bits prior valid =
  trans
    (finiteCNFCookNewestGateExact (Circuit.constantGate value) bits)
    (Original.placedGateOutputForced (Circuit.constantGate value) bits valid)
finiteCNFPlacedGateOriginalStep (Circuit.notGate source) bits prior valid =
  trans
    (trans
      (finiteCNFCookNewestGateExact (Circuit.notGate source) bits)
      (Original.placedGateOutputForced (Circuit.notGate source) bits valid))
    (cong Cook.notBool
      (finiteCNFWindowWireValue
        (Circuit.notGate source) bits prior source
        (fsuc fzero) refl))
finiteCNFPlacedGateOriginalStep (Circuit.andGate left right) bits prior valid =
  trans
    (trans
      (finiteCNFCookNewestGateExact (Circuit.andGate left right) bits)
      (Original.placedGateOutputForced (Circuit.andGate left right) bits valid))
    (cong₂ Cook.andBool
      (finiteCNFWindowWireValue
        (Circuit.andGate left right) bits prior left
        (fsuc fzero) refl)
      (finiteCNFWindowWireValue
        (Circuit.andGate left right) bits prior right
        (fsuc (fsuc fzero)) refl))
finiteCNFPlacedGateOriginalStep (Circuit.orGate left right) bits prior valid =
  trans
    (trans
      (finiteCNFCookNewestGateExact (Circuit.orGate left right) bits)
      (Original.placedGateOutputForced (Circuit.orGate left right) bits valid))
    (cong₂ Cook.orBool
      (finiteCNFWindowWireValue
        (Circuit.orGate left right) bits prior left
        (fsuc fzero) refl)
      (finiteCNFWindowWireValue
        (Circuit.orGate left right) bits prior right
        (fsuc (fsuc fzero)) refl))

-- The imported original #1040 owner already proves both directions
-- once ProgramAssignmentRealizes is available. Remaining unpaid
-- induction glue: extend the prior realization from the old pulled-back
-- finite CNF to the new global assignment while preserving input and all
-- previously used gate values. Do not claim P1/P2 closed until then.


------------------------------------------------------------------------
-- P1 INDUCTION GLUE: extending the whole-program CNF by one gate preserves
-- all earlier variable VALUES in the ORIGINAL Cook.Assignment carrier.
-- Reuses exact old gate-numbering and original Fin placement.
------------------------------------------------------------------------

originalEarlierIndexNumberExact :
  ∀ {inputs gates : Nat}
    (index : Fin (inputs + gates)) →
  FinBase.toℕ (Original.extendEarlierFin index) ≡ FinBase.toℕ index
originalEarlierIndexNumberExact {inputs} {gates} index =
  FinP.toℕ-fromℕ<
    (NatP.<-trans
      (FinP.toℕ<n index)
      (Original.newOutputBelow {inputs} {gates}))

finiteCNFPrefixCookAgreement :
  ∀ {inputs gates : Nat}
    (bits : CNF.Bits (inputs + suc gates))
    (index : Fin (inputs + gates)) →
  finiteCNFToCookAssignment
    (Rename.pullbackBits Original.extendEarlierFin bits)
    (FinBase.toℕ index)
  ≡ finiteCNFToCookAssignment bits (FinBase.toℕ index)
finiteCNFPrefixCookAgreement bits index =
  trans
    (finiteCNFToCookLookup
      (Rename.pullbackBits Original.extendEarlierFin bits) index)
    (trans
      (Rename.pullbackLookup Original.extendEarlierFin bits index)
      (trans
        (sym
          (finiteCNFToCookLookup bits (Original.extendEarlierFin index)))
        (cong (finiteCNFToCookAssignment bits)
          (originalEarlierIndexNumberExact index))))

finLeftOriginalInputNumber :
  ∀ {inputs gates : Nat} (index : Fin inputs) →
  FinBase.toℕ (Placement.finLeft {n = gates} index) ≡
    FinBase.toℕ index
finLeftOriginalInputNumber {inputs = zero} ()
finLeftOriginalInputNumber {inputs = suc inputs} fzero = refl
finLeftOriginalInputNumber {inputs = suc inputs} {gates = gates} (fsuc index) =
  cong suc (finLeftOriginalInputNumber {gates = gates} index)

-- The actual dependent #1040 realization proof can be reused on an
-- enlarged global bit assignment without changing ANY previously
-- interpreted circuit inputs or gate outputs.
realizationTransportToExtendedBits :
  ∀ {inputs gates : Nat}
    {program : Circuit.GateProgram inputs gates}
    (bits : CNF.Bits (inputs + suc gates)) →
  Existing.ProgramAssignmentRealizes program
    (finiteCNFToCookAssignment
      (Rename.pullbackBits Original.extendEarlierFin bits)) →
  Existing.ProgramAssignmentRealizes program
    (finiteCNFToCookAssignment bits)
realizationTransportToExtendedBits {inputs} {gates}
    {program} bits previousRealization =
  Existing.program-assignment-realizes
    (Existing.inputValues previousRealization)
    (λ index →
      trans
        (sym (inputAssignmentPrefixAgreement index))
        (Existing.inputVariablesCorrect previousRealization index))
    (λ index →
      trans
        (sym (gateAssignmentPrefixAgreement index))
        (Existing.gateVariablesCorrect previousRealization index))
  where
    oldAssignment = finiteCNFToCookAssignment
      (Rename.pullbackBits Original.extendEarlierFin bits)
    newAssignment = finiteCNFToCookAssignment bits

    inputAssignmentPrefixAgreement :
      (index : Fin inputs) →
      oldAssignment (FinBase.toℕ index) ≡
      newAssignment (FinBase.toℕ index)
    inputAssignmentPrefixAgreement index =
      trans
        (cong oldAssignment
          (sym (finLeftOriginalInputNumber {gates = gates} index)))
        (trans
          (finiteCNFPrefixCookAgreement bits
            (Placement.finLeft {n = gates} index))
          (cong newAssignment
            (finLeftOriginalInputNumber {gates = gates} index)))

    gateAssignmentPrefixAgreement :
      (index : Fin gates) →
      oldAssignment (Compiler.gateVariableIndex inputs index) ≡
      newAssignment (Compiler.gateVariableIndex inputs index)
    gateAssignmentPrefixAgreement index =
      trans
        (cong oldAssignment
          (sym (FinP.toℕ-fromℕ<
            (Existing.gateVariableIndexBelowNext inputs index))))
        (trans
          (finiteCNFPrefixCookAgreement bits
            (FinBase.fromℕ<
              (Existing.gateVariableIndexBelowNext inputs index)))
          (cong newAssignment
            (FinP.toℕ-fromℕ<
              (Existing.gateVariableIndexBelowNext inputs index))))

-- This is the hard same-assignment prefix bridge, *not* a proof that all
-- bits satisfy a circuit. It enables the direct existing realization
-- induction below rather than repeating the circuit evaluator in Agda.


------------------------------------------------------------------------
-- P1 GLOBAL SOUNDNESS: use the pre-existing (2026-09 #1040) ORIGINAL
-- ProgramAssignmentRealizes source, not a second circuit evaluator.
-- Every new gate has already been proved functional, and the earlier
-- realization is preserved by the prefix-transport lemma just above.
------------------------------------------------------------------------

finiteCNFCookInputAtSourceNumber :
  ∀ {inputs gates : Nat}
    (bits : CNF.Bits (inputs + gates))
    (index : Fin inputs) →
  finiteCNFToCookAssignment bits (FinBase.toℕ index)
    ≡ Circuit.lookupVec index (inputVectorFromGlobal bits)
finiteCNFCookInputAtSourceNumber {gates = gates} bits index =
  trans
    (cong (finiteCNFToCookAssignment bits)
      (sym (finLeftOriginalInputNumber {gates = gates} index)))
    (finiteCNFCookInputExact bits index)

globalPlacedProgramGivesOriginalRealization :
  ∀ {inputs gates : Nat}
    (program : Circuit.GateProgram inputs gates)
    (bits : CNF.Bits (inputs + gates)) →
  Original.ProgramPlacedGatesValid program bits →
  Existing.ProgramAssignmentRealizes program
    (finiteCNFToCookAssignment bits)
globalPlacedProgramGivesOriginalRealization
    Circuit.noGates bits Original.emptyProgramValid =
  Existing.program-assignment-realizes
    (inputVectorFromGlobal bits)
    (finiteCNFCookInputAtSourceNumber bits)
    (λ ())
globalPlacedProgramGivesOriginalRealization
    {inputs = inputs} {gates = suc gates}
    (Circuit.appendGate previous gate)
    bits
    (Original.extendedProgramValid oldValid gateValid) =
  Existing.program-assignment-realizes
    (Existing.inputValues lifted)
    (Existing.inputVariablesCorrect lifted)
    gateCorrect
  where
    oldRealization =
      globalPlacedProgramGivesOriginalRealization
        previous
        (Rename.pullbackBits Original.extendEarlierFin bits)
        oldValid
    lifted =
      realizationTransportToExtendedBits bits oldRealization

    gateCorrect :
      (index : Fin (suc gates)) →
      finiteCNFToCookAssignment bits
        (Compiler.gateVariableIndex inputs index)
      ≡ Circuit.lookupVec index
        (Circuit.evaluateProgram
          (Circuit.appendGate previous gate)
          (Existing.inputValues lifted))
    gateCorrect fzero =
      finiteCNFPlacedGateOriginalStep gate bits lifted gateValid
    gateCorrect (fsuc index) =
      Existing.gateVariablesCorrect lifted index

-- Uniqueness of input interpretation for any pre-existing realization.
-- This reuses prior #1040's field-level input correctness and the Q1
-- source's vector extensionality, not a new extensionality axiom.
realizationInputsAreGlobalPrefix :
  ∀ {inputs gates : Nat}
    {program : Circuit.GateProgram inputs gates}
    (bits : CNF.Bits (inputs + gates))
    (realization : Existing.ProgramAssignmentRealizes program
      (finiteCNFToCookAssignment bits)) →
  Existing.inputValues realization ≡ inputVectorFromGlobal bits
realizationInputsAreGlobalPrefix bits realization =
  VectorOwner.vecExtensionality
    (Existing.inputValues realization)
    (inputVectorFromGlobal bits)
    (λ index →
      trans
        (sym (Existing.inputVariablesCorrect realization index))
        (finiteCNFCookInputAtSourceNumber bits index))

-- The output wire is read using the same original compiler variable
-- number. No extra variable is introduced by this proof or by the CNF.
finiteCookAtCircuitOutput :
  ∀ {inputs gates : Nat}
    (wire : Circuit.WireRef inputs gates)
    (bits : CNF.Bits (inputs + gates)) →
  finiteCNFToCookAssignment bits (Original.wireNumber wire)
    ≡ CNF.lookupBit bits (Original.outputWireFin wire)
finiteCookAtCircuitOutput wire bits =
  trans
    (cong (finiteCNFToCookAssignment bits)
      (sym
        (FinP.toℕ-fromℕ<
          (Original.wireNumberBelowAtCircuitEnd wire))))
    (finiteCNFToCookLookup bits (Original.outputWireFin wire))

-- THE LITERAL GLOBAL-SOUNDNESS RESULT: every model of the ORIGINAL
-- assembled 3-CNF has an accepted original circuit input valuation.
-- No cardinality statement or converse is silently inferred.
originalPlacedCNFImpliesAcceptedInput :
  ∀ {inputs : Nat}
    (circuit : Circuit.ConcreteBooleanCircuit inputs)
    (bits : CNF.Bits (inputs + Circuit.gateCount circuit)) →
  CNF.evaluateCNF (Original.circuitPlacedCNF circuit) bits ≡ true →
  Circuit.evaluateCircuit circuit (inputVectorFromGlobal bits) ≡ true
originalPlacedCNFImpliesAcceptedInput circuit bits accepted =
  trans
    (sym (cong (Circuit.evaluateCircuit circuit)
      (realizationInputsAreGlobalPrefix bits realization)))
    (trans
      (sym
        (Existing.wireFormulaCorrect realization
          (Circuit.outputWire circuit)))
      (trans
        (finiteCookAtCircuitOutput (Circuit.outputWire circuit) bits)
        (Original.WholeCircuitPlacedMeaning.outputAccepted meaning)))
  where
    meaning = Original.wholeCircuitPlacedCNFSound circuit bits accepted
    realization = globalPlacedProgramGivesOriginalRealization
      (Circuit.program circuit) bits
      (Original.WholeCircuitPlacedMeaning.gateRelations meaning)

-- SOURCE-WRITTEN GLOBAL SOUNDNESS, NOT YET AGDA KERNEL VERIFIED.
-- Converse and P2 numerical #SAT equality still require completeness
-- against canonical original gate assignments. Reuse previous original
-- Semantics.canonicalProgramRealization and source fixed-bit codec for it.


------------------------------------------------------------------------
-- P1 CONVERSE: a model satisfying the ORIGINAL #1040 circuit realization
-- invariant induces the EXACT existing placed 3-CNF gate relations.
------------------------------------------------------------------------

finiteCookPrefixInputAgreement :
  ∀ {inputs gates : Nat}
    (bits : CNF.Bits (inputs + suc gates))
    (index : Fin inputs) →
  finiteCNFToCookAssignment
    (Rename.pullbackBits Original.extendEarlierFin bits)
    (FinBase.toℕ index)
  ≡ finiteCNFToCookAssignment bits (FinBase.toℕ index)
finiteCookPrefixInputAgreement {gates = gates} bits index =
  trans
    (cong
      (finiteCNFToCookAssignment
        (Rename.pullbackBits Original.extendEarlierFin bits))
      (sym (finLeftOriginalInputNumber {gates = gates} index)))
    (trans
      (finiteCNFPrefixCookAgreement bits
        (Placement.finLeft {n = gates} index))
      (cong (finiteCNFToCookAssignment bits)
        (finLeftOriginalInputNumber {gates = gates} index)))

finiteCookPrefixGateAgreement :
  ∀ {inputs gates : Nat}
    (bits : CNF.Bits (inputs + suc gates))
    (index : Fin gates) →
  finiteCNFToCookAssignment
    (Rename.pullbackBits Original.extendEarlierFin bits)
    (Compiler.gateVariableIndex inputs index)
  ≡ finiteCNFToCookAssignment bits
    (Compiler.gateVariableIndex inputs index)
finiteCookPrefixGateAgreement {inputs} bits index =
  trans
    (cong
      (finiteCNFToCookAssignment
        (Rename.pullbackBits Original.extendEarlierFin bits))
      (sym (FinP.toℕ-fromℕ<
        (Existing.gateVariableIndexBelowNext inputs index))))
    (trans
      (finiteCNFPrefixCookAgreement bits
        (FinBase.fromℕ<
          (Existing.gateVariableIndexBelowNext inputs index)))
      (cong (finiteCNFToCookAssignment bits)
        (FinP.toℕ-fromℕ<
          (Existing.gateVariableIndexBelowNext inputs index))))

realizationTransportToPrefixBits :
  ∀ {inputs gates : Nat}
    {program : Circuit.GateProgram inputs gates}
    (bits : CNF.Bits (inputs + suc gates)) →
  Existing.ProgramAssignmentRealizes program
    (finiteCNFToCookAssignment bits) →
  Existing.ProgramAssignmentRealizes program
    (finiteCNFToCookAssignment
      (Rename.pullbackBits Original.extendEarlierFin bits))
realizationTransportToPrefixBits bits realization =
  Existing.program-assignment-realizes
    (Existing.inputValues realization)
    (λ index →
      trans
        (finiteCookPrefixInputAgreement bits index)
        (Existing.inputVariablesCorrect realization index))
    (λ index →
      trans
        (finiteCookPrefixGateAgreement bits index)
        (Existing.gateVariablesCorrect realization index))

finiteCNFExpectedGateFromRealization :
  ∀ {inputs gates : Nat}
    {previous : Circuit.GateProgram inputs gates}
    (gate : Circuit.Gate inputs gates)
    (bits : CNF.Bits (inputs + suc gates))
    (prior : Existing.ProgramAssignmentRealizes previous
      (finiteCNFToCookAssignment bits)) →
  Original.localGateExpectedOutput gate
    (Rename.pullbackBits (Original.gateWindowRename gate) bits)
    ≡ Circuit.evaluateGate gate
      (Existing.inputValues prior)
      (Circuit.evaluateProgram previous (Existing.inputValues prior))
finiteCNFExpectedGateFromRealization (Circuit.constantGate value) bits prior =
  refl
finiteCNFExpectedGateFromRealization (Circuit.notGate source) bits prior =
  cong Cook.notBool
    (finiteCNFWindowWireValue
      (Circuit.notGate source) bits prior source
      (fsuc fzero) refl)
finiteCNFExpectedGateFromRealization (Circuit.andGate left right) bits prior =
  cong₂ Cook.andBool
    (finiteCNFWindowWireValue
      (Circuit.andGate left right) bits prior left
      (fsuc fzero) refl)
    (finiteCNFWindowWireValue
      (Circuit.andGate left right) bits prior right
      (fsuc (fsuc fzero)) refl)
finiteCNFExpectedGateFromRealization (Circuit.orGate left right) bits prior =
  cong₂ Cook.orBool
    (finiteCNFWindowWireValue
      (Circuit.orGate left right) bits prior left
      (fsuc fzero) refl)
    (finiteCNFWindowWireValue
      (Circuit.orGate left right) bits prior right
      (fsuc (fsuc fzero)) refl)

finiteCNFGateRelationFromOriginalRealization :
  ∀ {inputs gates : Nat}
    {previous : Circuit.GateProgram inputs gates}
    (gate : Circuit.Gate inputs gates)
    (bits : CNF.Bits (inputs + suc gates)) →
  Existing.ProgramAssignmentRealizes
    (Circuit.appendGate previous gate)
    (finiteCNFToCookAssignment bits) →
  Original.localGateConsistent gate
    (Rename.pullbackBits (Original.gateWindowRename gate) bits) ≡ true
finiteCNFGateRelationFromOriginalRealization
    gate bits realization =
  Original.placedGateOutputComplete gate bits
    (trans
      (sym (finiteCNFCookNewestGateExact gate bits))
      (trans
        (Existing.gateVariablesCorrect realization fzero)
        (sym (finiteCNFExpectedGateFromRealization
          gate bits (Existing.previousRealization realization)))))

globalOriginalRealizationGivesPlacedValid :
  ∀ {inputs gates : Nat}
    (program : Circuit.GateProgram inputs gates)
    (bits : CNF.Bits (inputs + gates)) →
  Existing.ProgramAssignmentRealizes program
    (finiteCNFToCookAssignment bits) →
  Original.ProgramPlacedGatesValid program bits
globalOriginalRealizationGivesPlacedValid
    Circuit.noGates bits realization =
  Original.emptyProgramValid
globalOriginalRealizationGivesPlacedValid
    (Circuit.appendGate previous gate)
    bits realization =
  Original.extendedProgramValid
    (globalOriginalRealizationGivesPlacedValid
      previous
      (Rename.pullbackBits Original.extendEarlierFin bits)
      (realizationTransportToPrefixBits bits
        (Existing.previousRealization realization)))
    (finiteCNFGateRelationFromOriginalRealization
      gate bits realization)

-- This provides both directions for ProgramPlacedGatesValid versus the
-- original earlier-source ProgramAssignmentRealizes on the same finite
-- assignment. The circuit-output unit and numeric counting still require
-- a canonical finite supported witness and a finite-sum transport.


------------------------------------------------------------------------
-- P1 COMPLETE SAT EQUIVALENCE: reuse the 2026-09 #1040 canonical
-- assignmentFromProgram (which ALREADY computes chronological gate values)
-- and tabulate it as the current source's exact finite CNF.Bits carrier.
-- No extra evaluator and no reversed-gate shadow encoding is invented.
------------------------------------------------------------------------

canonicalOriginalProgramBits :
  ∀ {inputs gates : Nat}
    (program : Circuit.GateProgram inputs gates)
    (values : Vec Bool inputs) →
  CNF.Bits (inputs + gates)
canonicalOriginalProgramBits program values =
  Rename.tabulateBits
    (λ index →
      Existing.assignmentFromProgram program values
        (FinBase.toℕ index))

canonicalOriginalProgramBitLookup :
  ∀ {inputs gates : Nat}
    (program : Circuit.GateProgram inputs gates)
    (values : Vec Bool inputs)
    (index : Fin (inputs + gates)) →
  finiteCNFToCookAssignment
    (canonicalOriginalProgramBits program values)
    (FinBase.toℕ index)
  ≡ Existing.assignmentFromProgram program values
    (FinBase.toℕ index)
canonicalOriginalProgramBitLookup program values index =
  trans
    (finiteCNFToCookLookup
      (canonicalOriginalProgramBits program values) index)
    (Rename.lookupTabulateBits
      (λ i → Existing.assignmentFromProgram program values
        (FinBase.toℕ i)) index)

canonicalOriginalProgramFiniteRealization :
  ∀ {inputs gates : Nat}
    (program : Circuit.GateProgram inputs gates)
    (values : Vec Bool inputs) →
  Existing.ProgramAssignmentRealizes program
    (finiteCNFToCookAssignment
      (canonicalOriginalProgramBits program values))
canonicalOriginalProgramFiniteRealization
    {inputs} {gates} program values =
  Existing.program-assignment-realizes
    values
    inputCorrect
    gateCorrect
  where
    bits = canonicalOriginalProgramBits program values
    originalAssignment = Existing.assignmentFromProgram program values

    inputCorrect :
      (index : Fin inputs) →
      finiteCNFToCookAssignment bits (FinBase.toℕ index)
        ≡ Circuit.lookupVec index values
    inputCorrect index =
      trans
        (cong (finiteCNFToCookAssignment bits)
          (sym (finLeftOriginalInputNumber {gates = gates} index)))
        (trans
          (canonicalOriginalProgramBitLookup
            program values (Placement.finLeft {n = gates} index))
          (trans
            (cong originalAssignment
              (finLeftOriginalInputNumber {gates = gates} index))
            (Existing.assignmentFromProgramInputCorrect
              program values index)))

    gateCorrect :
      (index : Fin gates) →
      finiteCNFToCookAssignment bits
        (Compiler.gateVariableIndex inputs index)
      ≡ Circuit.lookupVec index (Circuit.evaluateProgram program values)
    gateCorrect index =
      trans
        (cong (finiteCNFToCookAssignment bits)
          (sym (FinP.toℕ-fromℕ<
            (Existing.gateVariableIndexBelowNext inputs index))))
        (trans
          (canonicalOriginalProgramBitLookup
            program values
            (FinBase.fromℕ<
              (Existing.gateVariableIndexBelowNext inputs index)))
          (trans
            (cong originalAssignment
              (FinP.toℕ-fromℕ<
                (Existing.gateVariableIndexBelowNext inputs index)))
            (Existing.assignmentFromProgramGateCorrect
              program values index)))

canonicalOriginalOutputValue :
  ∀ {inputs : Nat}
    (circuit : Circuit.ConcreteBooleanCircuit inputs)
    (values : Vec Bool inputs) →
  CNF.lookupBit
    (canonicalOriginalProgramBits (Circuit.program circuit) values)
    (Original.outputWireFin (Circuit.outputWire circuit))
  ≡ Circuit.evaluateCircuit circuit values
canonicalOriginalOutputValue circuit values =
  trans
    (Rename.lookupTabulateBits
      (λ i → Existing.assignmentFromProgram (Circuit.program circuit)
        values (FinBase.toℕ i))
      (Original.outputWireFin (Circuit.outputWire circuit)))
    (trans
      (cong (Existing.assignmentFromProgram
        (Circuit.program circuit) values)
        (FinP.toℕ-fromℕ<
          (Original.wireNumberBelowAtCircuitEnd
            (Circuit.outputWire circuit))))
      (Existing.canonicalOutputFormulaCorrect circuit values))

canonicalGlobalPlacedCNFCompleteness :
  ∀ {inputs : Nat}
    (circuit : Circuit.ConcreteBooleanCircuit inputs)
    (values : Vec Bool inputs) →
  Circuit.evaluateCircuit circuit values ≡ true →
  CNF.evaluateCNF (Original.circuitPlacedCNF circuit)
    (canonicalOriginalProgramBits (Circuit.program circuit) values)
    ≡ true
canonicalGlobalPlacedCNFCompleteness circuit values accepted =
  Original.wholeCircuitPlacedCNFComplete circuit
    (canonicalOriginalProgramBits (Circuit.program circuit) values)
    (Original.whole-circuit-placed-meaning
      (globalOriginalRealizationGivesPlacedValid
        (Circuit.program circuit)
        (canonicalOriginalProgramBits (Circuit.program circuit) values)
        (canonicalOriginalProgramFiniteRealization
          (Circuit.program circuit) values))
      (trans (canonicalOriginalOutputValue circuit values) accepted))

-- At the SAME concrete circuit:
--   compiled-CNF model -> source accepting input,
--   source accepting input -> compiled-CNF canonical model.
-- Both are source-written. The numerical model-count equality and
-- Agda-kernel acceptance remain separate obligations.


------------------------------------------------------------------------
-- P1 SAME-CIRCUIT GLOBAL 3-CNF SAT EQUIVALENCE, BOTH DIRECTIONS.
-- Quantifies the original finite carriers; no implicit Cook.Assignment
-- tail, no additional gate, no assumption about global model cardinality.
------------------------------------------------------------------------

OriginalPlacedCNFSatisfiable :
  ∀ {inputs : Nat} (circuit : Circuit.ConcreteBooleanCircuit inputs) →
  Set
OriginalPlacedCNFSatisfiable {inputs} circuit =
  Σ (CNF.Bits (inputs + Circuit.gateCount circuit))
    (λ bits → CNF.evaluateCNF (Original.circuitPlacedCNF circuit) bits
      ≡ true)

OriginalCircuitHasAcceptedInput :
  ∀ {inputs : Nat} (circuit : Circuit.ConcreteBooleanCircuit inputs) →
  Set
OriginalCircuitHasAcceptedInput {inputs} circuit =
  Σ (Vec Bool inputs)
    (λ values → Circuit.evaluateCircuit circuit values ≡ true)

originalPlacedCNFSatisfiabilityToCircuit :
  ∀ {inputs : Nat} (circuit : Circuit.ConcreteBooleanCircuit inputs) →
  OriginalPlacedCNFSatisfiable circuit →
  OriginalCircuitHasAcceptedInput circuit
originalPlacedCNFSatisfiabilityToCircuit circuit (bits , accepted) =
  inputVectorFromGlobal bits ,
  originalPlacedCNFImpliesAcceptedInput circuit bits accepted

originalCircuitToPlacedCNFSatisfiability :
  ∀ {inputs : Nat} (circuit : Circuit.ConcreteBooleanCircuit inputs) →
  OriginalCircuitHasAcceptedInput circuit →
  OriginalPlacedCNFSatisfiable circuit
originalCircuitToPlacedCNFSatisfiability circuit (values , accepted) =
  canonicalOriginalProgramBits (Circuit.program circuit) values ,
  canonicalGlobalPlacedCNFCompleteness circuit values accepted

-- Both logical implications are now SOURCE-WRITTEN against the actual
-- assembled CNF, not merely inherited from the Cook formula.
-- The stronger equation countSourceCNF C = countAcceptedCircuitInputs C
-- remains unpaid: multiple global assignments have to be proved
-- impossible at a given accepted input, and finite sums transported.


------------------------------------------------------------------------
-- The EXISTING compiler's newest-first indices are the stdlib Fin.opposite
-- of chronological suffix indices. Reuse FinP.opposite-involutive,
-- FinP.toℕ-fromℕ, FinP.toℕ-inject₁ and the existing Canonical right
-- embedding; never create a second gate-numbering convention.
------------------------------------------------------------------------

gateNumberEqualsOppositeIndex :
  ∀ (inputs : Nat) {gates : Nat} (index : Fin gates) →
  Compiler.gateVariableIndex inputs index ≡
    inputs + FinBase.toℕ (FinBase.opposite index)
gateNumberEqualsOppositeIndex inputs {gates = suc gates} fzero =
  cong (λ position → inputs + position)
    (sym (FinP.toℕ-fromℕ gates))
gateNumberEqualsOppositeIndex inputs {gates = suc gates} (fsuc index) =
  trans
    (gateNumberEqualsOppositeIndex inputs index)
    (cong (λ position → inputs + position)
      (sym (FinP.toℕ-inject₁ (FinBase.opposite index))))

chronologicalGateNumberExact :
  ∀ (inputs : Nat) {gates : Nat} (index : Fin gates) →
  Compiler.gateVariableIndex inputs (FinBase.opposite index) ≡
    inputs + FinBase.toℕ index
chronologicalGateNumberExact inputs index =
  trans
    (gateNumberEqualsOppositeIndex inputs (FinBase.opposite index))
    (cong (λ position → inputs + position)
      (FinP.opposite-involutive index))

finRightOriginalGateNumber :
  ∀ (inputs : Nat) {gates : Nat} (index : Fin gates) →
  FinBase.toℕ (Placement.finRight inputs index) ≡
    inputs + FinBase.toℕ index
finRightOriginalGateNumber zero index = refl
finRightOriginalGateNumber (suc inputs) index =
  cong suc (finRightOriginalGateNumber inputs index)

finiteCookChronologicalGateExact :
  ∀ {inputs gates : Nat}
    (bits : CNF.Bits (inputs + gates)) (index : Fin gates) →
  finiteCNFToCookAssignment bits
    (Compiler.gateVariableIndex inputs (FinBase.opposite index))
  ≡ CNF.lookupBit bits (Placement.finRight inputs index)
finiteCookChronologicalGateExact {inputs} bits index =
  trans
    (cong (finiteCNFToCookAssignment bits)
      (chronologicalGateNumberExact inputs index))
    (trans
      (cong (finiteCNFToCookAssignment bits)
        (sym (finRightOriginalGateNumber inputs index)))
      (finiteCNFToCookLookup bits
        (Placement.finRight inputs index)))

-- These are genuine typed index identities on the original finite support.
-- No absolute-size overhead, approximate graph theorem or ETH claim follows.
