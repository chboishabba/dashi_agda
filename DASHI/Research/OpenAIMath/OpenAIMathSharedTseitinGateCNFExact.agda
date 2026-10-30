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
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Vec.Base using (Vec)
open import Agda.Builtin.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; trans)
import Data.Fin.Base as Fin
import Data.Fin.Properties as FinP
open import Data.Nat.Base using (_<_)
import Data.Nat.Properties as NatP

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PNotEqualsNPConcreteBooleanCircuitDAGExact as Circuit
import DASHI.Mathematics.Complexity.FixedWidthTruthTableCNFExact as CNF
import DASHI.Mathematics.Complexity.CNFVariableRenamingExact as Rename
import DASHI.Mathematics.Complexity.CNFPlacedConstraintConjunctionExact as Placed
import DASHI.Mathematics.Complexity.CookLevinGridReplicationExact as Grid
import DASHI.Mathematics.Complexity.PNotEqualsNPConcreteCircuitSharedCompilerExact as Compiler
import DASHI.Mathematics.Complexity.PNotEqualsNPConcreteCircuitSharedSemanticsExact as Semantics

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


------------------------------------------------------------------------
-- CERTIFIED GLOBAL FIN-NAME PLACEMENT for ONE existing DAG gate.
--
-- Inputs use 0..inputs-1; earlier gates use exactly the original compiler's
-- creation-time numbers; new output uses inputs+gates.
-- CNFPlacedConstraintConjunctionExact and CNFVariableRenamingExact are
-- original owners of the compilation/renaming semantics. Nothing here
-- constructs an alternative CNF representation.
------------------------------------------------------------------------

newOutputBelow :
  ∀ {inputs gates : Nat} →
  inputs + gates < inputs + suc gates
newOutputBelow {inputs} {gates} =
  NatP.+-monoˡ-< inputs (NatP.n<1+n gates)

newOutputFin :
  ∀ {inputs gates : Nat} →
  Fin.Fin (inputs + suc gates)
newOutputFin {inputs} {gates} =
  Fin.fromℕ< (newOutputBelow {inputs} {gates})

-- Actual original compiler variable numbering, before injecting to Fin.
wireNumber :
  ∀ {inputs gates : Nat} →
  Circuit.WireRef inputs gates → Nat
wireNumber (Circuit.inputWire index) = Fin.toℕ index
wireNumber {inputs} (Circuit.gateWire index) =
  Compiler.gateVariableIndex inputs index

wireNumberBelow :
  ∀ {inputs gates : Nat}
    (source : Circuit.WireRef inputs gates) →
  wireNumber source < inputs + suc gates
wireNumberBelow {inputs} {gates} (Circuit.inputWire index) =
  NatP.<-≤-trans
    (FinP.toℕ<n index)
    (NatP.m≤m+n inputs (suc gates))
wireNumberBelow {inputs} {gates} (Circuit.gateWire index) =
  NatP.<-trans
    (Semantics.gateVariableIndexBelowNext inputs index)
    (newOutputBelow {inputs} {gates})

wireFin :
  ∀ {inputs gates : Nat} →
  Circuit.WireRef inputs gates → Fin.Fin (inputs + suc gates)
wireFin source = Fin.fromℕ< (wireNumberBelow source)

-- Only three finite indices per gate. Unused inputs of a constant/NOT gate
-- can harmlessly alias the output, because the local relation ignores them.
gateWindowRename :
  ∀ {inputs gates : Nat} →
  (gate : Circuit.Gate inputs gates) →
  Fin.Fin three → Fin.Fin (inputs + suc gates)
gateWindowRename gate Fin.zero = newOutputFin
gateWindowRename (Circuit.constantGate value) (Fin.suc Fin.zero) =
  newOutputFin
gateWindowRename (Circuit.constantGate value)
    (Fin.suc (Fin.suc Fin.zero)) =
  newOutputFin
gateWindowRename (Circuit.notGate source) (Fin.suc Fin.zero) =
  wireFin source
gateWindowRename (Circuit.notGate source)
    (Fin.suc (Fin.suc Fin.zero)) =
  newOutputFin
gateWindowRename (Circuit.andGate left right) (Fin.suc Fin.zero) =
  wireFin left
gateWindowRename (Circuit.andGate left right)
    (Fin.suc (Fin.suc Fin.zero)) =
  wireFin right
gateWindowRename (Circuit.orGate left right) (Fin.suc Fin.zero) =
  wireFin left
gateWindowRename (Circuit.orGate left right)
    (Fin.suc (Fin.suc Fin.zero)) =
  wireFin right

-- The output variable number agrees exactly with the ORIGINAL shared
-- Tseitin compiler, rather than merely being alpha-equivalent.
gateOutputIndexExact :
  ∀ {inputs gates : Nat}
    (gate : Circuit.Gate inputs gates) →
  Fin.toℕ (gateWindowRename gate Fin.zero) ≡ inputs + gates
gateOutputIndexExact {inputs} {gates} gate =
  FinP.toℕ-fromℕ< (newOutputBelow {inputs} {gates})

-- One original placed local constraint with the certified output/operand map.
placedGate :
  ∀ {inputs gates : Nat} →
  Circuit.Gate inputs gates →
  Placed.PlacedPredicate three (inputs + suc gates)
placedGate gate =
  Placed.placed-predicate
    (gateWindowRename gate)
    (localGateConsistent gate)

placedGateCNF :
  ∀ {inputs gates : Nat} →
  Circuit.Gate inputs gates →
  CNF.CNF (inputs + suc gates)
placedGateCNF gate = Placed.compilePlaced (placedGate gate)

-- All soundness/completeness is imported from the previously developed
-- original CNF placement theorem, not rederived gate by gate.
placedGateSound :
  ∀ {inputs gates : Nat}
    (gate : Circuit.Gate inputs gates)
    (globalBits : CNF.Bits (inputs + suc gates)) →
  CNF.evaluateCNF (placedGateCNF gate) globalBits ≡ true →
  localGateConsistent gate
    (Rename.pullbackBits (gateWindowRename gate) globalBits) ≡ true
placedGateSound gate globalBits =
  Rename.placedTruthTableCNFSound
    (gateWindowRename gate) (localGateConsistent gate) globalBits

placedGateComplete :
  ∀ {inputs gates : Nat}
    (gate : Circuit.Gate inputs gates)
    (globalBits : CNF.Bits (inputs + suc gates)) →
  localGateConsistent gate
    (Rename.pullbackBits (gateWindowRename gate) globalBits) ≡ true →
  CNF.evaluateCNF (placedGateCNF gate) globalBits ≡ true
placedGateComplete gate globalBits =
  Rename.placedTruthTableCNFComplete
    (gateWindowRename gate) (localGateConsistent gate) globalBits

-- Next: assemble GateProgram by renaming previous clauses into the new
-- finite global width, conjoin one placed gate, add final output literal,
-- prove uniqueness/parsimonious count using the established numeric result.
-- No global #SAT or OpenAI bit length claim follows yet from one gate.


------------------------------------------------------------------------
-- A sharper resource fact than the generic 8-row upper bound:
-- every one of these four concrete DAG gate forms rejects exactly four
-- of the eight possible 3-bit windows. The original Grid owner supplies
-- the clause-length measure; this is a fixed finite reduction by computation.
------------------------------------------------------------------------

four : Nat
four = suc (suc (suc (suc zero)))

localGateCNFClauseCountFour :
  ∀ {inputs gates : Nat}
    (gate : Circuit.Gate inputs gates) →
  Grid.listLength (localGateCNF gate) ≡ four
localGateCNFClauseCountFour (Circuit.constantGate false) = refl
localGateCNFClauseCountFour (Circuit.constantGate true) = refl
localGateCNFClauseCountFour (Circuit.notGate source) = refl
localGateCNFClauseCountFour (Circuit.andGate left right) = refl
localGateCNFClauseCountFour (Circuit.orGate left right) = refl

-- Actual proof: original renameCNF maps clauses one-to-one, and the
-- original Grid.listLength counts clauses independently of their literals.
renameCNFClauseCountExact :
  ∀ {local global : Nat}
    (renaming : Fin.Fin local → Fin.Fin global)
    (formula : CNF.CNF local) →
  Grid.listLength (Rename.renameCNF renaming formula)
    ≡ Grid.listLength formula
renameCNFClauseCountExact renaming [] = refl
renameCNFClauseCountExact renaming (clause ∷ clauses) =
  cong suc (renameCNFClauseCountExact renaming clauses)

placedGateCNFClauseCountFour :
  ∀ {inputs gates : Nat}
    (gate : Circuit.Gate inputs gates) →
  Grid.listLength (placedGateCNF gate) ≡ four
placedGateCNFClauseCountFour gate =
  trans
    (renameCNFClauseCountExact
      (gateWindowRename gate) (localGateCNF gate))
    (localGateCNFClauseCountFour gate)

-- This is an actual same-object clause-count transport from the source
-- gate to its ORIGINAL placed CNF. Agda kernel verification pending.


------------------------------------------------------------------------
-- WHOLE CONCRETE DAG -> GLOBAL CNF, REUSING THE PRIOR PLACEMENT/APPEND
-- OWNERS AND THE EXISTING CREATION-TIME GATE INDEXING. No new CNF datatype.
------------------------------------------------------------------------

-- Old circuit variables retain their identical numeric position when the
-- next gate adds ONE fresh output variable at the end.
extendEarlierFin :
  ∀ {inputs gates : Nat} →
  Fin.Fin (inputs + gates) → Fin.Fin (inputs + suc gates)
extendEarlierFin {inputs} {gates} index =
  Fin.fromℕ<
    (NatP.<-trans
      (FinP.toℕ<n index)
      (newOutputBelow {inputs} {gates}))

-- Structural, input-size-uniform assembly: each prior fixed-width clause
-- is transported unchanged to a larger finite variable universe, and the
-- new placed gate contributes its own four clauses.
programPlacedCNF :
  ∀ {inputs gates : Nat} →
  Circuit.GateProgram inputs gates → CNF.CNF (inputs + gates)
programPlacedCNF Circuit.noGates = []
programPlacedCNF
    (Circuit.appendGate previous gate) =
  Placed.append
    (Rename.renameCNF extendEarlierFin (programPlacedCNF previous))
    (placedGateCNF gate)

-- Two older source owners define extensionally equal append functions,
-- but unknown lists do not make their bodies definitionally identical.
-- Prove the EXACT append used by the placed-constraint owner.
placedAppendLength :
  ∀ {A : Set} (left right : List A) →
  Grid.listLength (Placed.append left right)
    ≡ Grid.listLength left + Grid.listLength right
placedAppendLength [] right = refl
placedAppendLength (value ∷ left) right =
  cong suc (placedAppendLength left right)

-- Canonical additive 4-per-gate clause budget. This is an actual
-- structural count, not a floating asymptotic assertion.
fourPerGate : Nat → Nat
fourPerGate zero = zero
fourPerGate (suc gates) = fourPerGate gates + four

programPlacedCNFClauseCount :
  ∀ {inputs gates : Nat}
    (program : Circuit.GateProgram inputs gates) →
  Grid.listLength (programPlacedCNF program) ≡ fourPerGate gates
programPlacedCNFClauseCount Circuit.noGates = refl
programPlacedCNFClauseCount
    (Circuit.appendGate previous gate) =
  trans
    (placedAppendLength
      (Rename.renameCNF extendEarlierFin (programPlacedCNF previous))
      (placedGateCNF gate))
    (cong₂ _+_
      (trans
        (renameCNFClauseCountExact
          extendEarlierFin (programPlacedCNF previous))
        (programPlacedCNFClauseCount previous))
      (placedGateCNFClauseCountFour gate))

-- The output wire already belongs to the n+g finite variable universe.
-- Reuse the same compiler numbering; DO NOT introduce a new output var.
wireNumberBelowAtCircuitEnd :
  ∀ {inputs gates : Nat}
    (source : Circuit.WireRef inputs gates) →
  wireNumber source < inputs + gates
wireNumberBelowAtCircuitEnd {inputs} {gates}
    (Circuit.inputWire index) =
  NatP.<-≤-trans
    (FinP.toℕ<n index)
    (NatP.m≤m+n inputs gates)
wireNumberBelowAtCircuitEnd {inputs} {gates}
    (Circuit.gateWire index) =
  Semantics.gateVariableIndexBelowNext inputs index

outputWireFin :
  ∀ {inputs gates : Nat} →
  Circuit.WireRef inputs gates → Fin.Fin (inputs + gates)
outputWireFin wire =
  Fin.fromℕ< (wireNumberBelowAtCircuitEnd wire)

outputUnitCNF :
  ∀ {inputs : Nat} →
  (circuit : Circuit.ConcreteBooleanCircuit inputs) →
  CNF.CNF (inputs + Circuit.gateCount circuit)
outputUnitCNF circuit =
  (CNF.positive (outputWireFin (Circuit.outputWire circuit)) ∷ [])
  ∷ []

-- The complete ORIGINAL DAG is compiled as already-placed gate clauses
-- followed by the required acceptance/output unit clause.
circuitPlacedCNF :
  ∀ {inputs : Nat} →
  (circuit : Circuit.ConcreteBooleanCircuit inputs) →
  CNF.CNF (inputs + Circuit.gateCount circuit)
circuitPlacedCNF circuit =
  Placed.append
    (programPlacedCNF (Circuit.program circuit))
    (outputUnitCNF circuit)

outputUnitCNFClauseCount :
  ∀ {inputs : Nat}
    (circuit : Circuit.ConcreteBooleanCircuit inputs) →
  Grid.listLength (outputUnitCNF circuit) ≡ suc zero
outputUnitCNFClauseCount circuit = refl

-- Exact total: 4 clauses per original DAG gate, plus ONE output unit.
circuitPlacedCNFClauseCount :
  ∀ {inputs : Nat}
    (circuit : Circuit.ConcreteBooleanCircuit inputs) →
  Grid.listLength (circuitPlacedCNF circuit)
    ≡ fourPerGate (Circuit.gateCount circuit) + suc zero
circuitPlacedCNFClauseCount circuit =
  trans
    (placedAppendLength
      (programPlacedCNF (Circuit.program circuit))
      (outputUnitCNF circuit))
    (cong₂ _+_
      (programPlacedCNFClauseCount (Circuit.program circuit))
      (outputUnitCNFClauseCount circuit))

-- All clauses in the programme are fixed-width, with no truth-table
-- expansion in the original input dimension. Exact solution-set equivalence
-- and global numeric #SAT parsimony remain the next proof obligations;
-- this commit proves the syntax and uniform clause count at source level.


------------------------------------------------------------------------
-- Closed-form cost, not only a recursive English "four per gate".
-- Reuse the existing standard Nat commutativity theorem; no arithmetic
-- algebra is re-proved for the local CNF.
------------------------------------------------------------------------

fourPerGateMultiply :
  (gates : Nat) → fourPerGate gates ≡ gates * four
fourPerGateMultiply zero = refl
fourPerGateMultiply (suc gates) =
  trans
    (cong (λ total → total + four)
      (fourPerGateMultiply gates))
    (NatP.+-comm (gates * four) four)

circuitPlacedCNFClosedClauseCount :
  ∀ {inputs : Nat}
    (circuit : Circuit.ConcreteBooleanCircuit inputs) →
  Grid.listLength (circuitPlacedCNF circuit) ≡
    Circuit.gateCount circuit * four + suc zero
circuitPlacedCNFClosedClauseCount circuit =
  trans
    (circuitPlacedCNFClauseCount circuit)
    (cong
      (λ total → total + suc zero)
      (fourPerGateMultiply (Circuit.gateCount circuit)))


------------------------------------------------------------------------
-- ACTUAL GLOBAL CNF SOUNDNESS / COMPLETENESS FOR THE ORIGINAL DAG.
--
-- This is a structural same-object statement: every assigned gate output
-- satisfies the original gate's local Boolean relation after pulling the
-- actual global Fin assignment back along its original variable indices.
-- Critically, this does not *yet* identify the finite assignment with
-- evaluateProgram on the input vector: that requires a separate
-- gate-evaluation/finite-bits bridge before transferring the numeric count.
--
-- Original proof owners reused:
--   Placed.evaluateCNFAppend
--   Rename.renamedCNFEvaluation
--   Rename.placedTruthTableCNFSound/Complete
--   CNF.andTrueGivesRight
-- No new SAT datatype, CNF compiler, or axiom.
------------------------------------------------------------------------

-- Same Boolean conjunction inversion, specialized to the earlier CNF owner.
-- The Cook-specific andTrueLeft lives in the prior SAT semantics owner; this
-- variant avoids silently assuming Cook.andBool and CNF.andBool are identical.
cnfAndTrueLeft :
  ∀ {left right : Bool} →
  CNF.andBool left right ≡ true → left ≡ true
cnfAndTrueLeft {true} {true} accepted = refl
cnfAndTrueLeft {true} {false} ()
cnfAndTrueLeft {false} {true} ()
cnfAndTrueLeft {false} {false} ()

cnfAndBothTrue :
  ∀ {left right : Bool} →
  left ≡ true → right ≡ true →
  CNF.andBool left right ≡ true
cnfAndBothTrue refl refl = refl

-- Proven structural witness for the ACTUAL original GateProgram, using
-- the concrete original local gate relation (not a synthetic oracle).
data ProgramPlacedGatesValid {inputs : Nat} :
  ∀ {gates : Nat} →
  (program : Circuit.GateProgram inputs gates) →
  CNF.Bits (inputs + gates) → Set where

  emptyProgramValid :
    ∀ {bits : CNF.Bits (inputs + zero)} →
    ProgramPlacedGatesValid Circuit.noGates bits

  extendedProgramValid :
    ∀ {gates : Nat}
      {previous : Circuit.GateProgram inputs gates}
      {gate : Circuit.Gate inputs gates}
      {bits : CNF.Bits (inputs + suc gates)} →
    ProgramPlacedGatesValid previous
      (Rename.pullbackBits extendEarlierFin bits) →
    localGateConsistent gate
      (Rename.pullbackBits (gateWindowRename gate) bits) ≡ true →
    ProgramPlacedGatesValid (Circuit.appendGate previous gate) bits

programPlacedCNFSound :
  ∀ {inputs gates : Nat}
    (program : Circuit.GateProgram inputs gates)
    (bits : CNF.Bits (inputs + gates)) →
  CNF.evaluateCNF (programPlacedCNF program) bits ≡ true →
  ProgramPlacedGatesValid program bits
programPlacedCNFSound Circuit.noGates bits accepted =
  emptyProgramValid
programPlacedCNFSound
    (Circuit.appendGate previous gate) bits accepted =
  extendedProgramValid
    (programPlacedCNFSound
      previous
      (Rename.pullbackBits extendEarlierFin bits)
      (trans
        (sym
          (Rename.renamedCNFEvaluation
            extendEarlierFin (programPlacedCNF previous) bits))
        (cnfAndTrueLeft split)))
    (placedGateSound gate bits
      (CNF.andTrueGivesRight
        (CNF.evaluateCNF
          (Rename.renameCNF extendEarlierFin
            (programPlacedCNF previous))
          bits)
        (CNF.evaluateCNF (placedGateCNF gate) bits)
        split))
  where
    split :
      CNF.andBool
        (CNF.evaluateCNF
          (Rename.renameCNF extendEarlierFin
            (programPlacedCNF previous))
          bits)
        (CNF.evaluateCNF (placedGateCNF gate) bits)
      ≡ true
    split =
      trans
        (sym
          (Placed.evaluateCNFAppend
            (Rename.renameCNF extendEarlierFin
              (programPlacedCNF previous))
            (placedGateCNF gate)
            bits))
        accepted

programPlacedCNFComplete :
  ∀ {inputs gates : Nat}
    (program : Circuit.GateProgram inputs gates)
    (bits : CNF.Bits (inputs + gates)) →
  ProgramPlacedGatesValid program bits →
  CNF.evaluateCNF (programPlacedCNF program) bits ≡ true
programPlacedCNFComplete Circuit.noGates bits emptyProgramValid = refl
programPlacedCNFComplete
    (Circuit.appendGate previous gate)
    bits
    (extendedProgramValid oldValid gateValid) =
  trans
    (Placed.evaluateCNFAppend
      (Rename.renameCNF extendEarlierFin
        (programPlacedCNF previous))
      (placedGateCNF gate)
      bits)
    (cnfAndBothTrue
      (trans
        (Rename.renamedCNFEvaluation
          extendEarlierFin
          (programPlacedCNF previous)
          bits)
        (programPlacedCNFComplete
          previous
          (Rename.pullbackBits extendEarlierFin bits)
          oldValid))
      (placedGateComplete gate bits gateValid))

-- The original output-wire unit clause has exactly the value of the
-- original output variable. Evaluating the Boolean bit explicitly avoids
-- an unproved rewrite between separately defined Boolean operations.
outputUnitEvaluation :
  ∀ {inputs : Nat}
    (circuit : Circuit.ConcreteBooleanCircuit inputs)
    (bits : CNF.Bits (inputs + Circuit.gateCount circuit)) →
  CNF.evaluateCNF (outputUnitCNF circuit) bits ≡
    CNF.lookupBit bits (outputWireFin (Circuit.outputWire circuit))
outputUnitEvaluation circuit bits
  with CNF.lookupBit bits (outputWireFin (Circuit.outputWire circuit))
... | false = refl
... | true = refl

record WholeCircuitPlacedMeaning
    {inputs : Nat}
    (circuit : Circuit.ConcreteBooleanCircuit inputs)
    (bits : CNF.Bits (inputs + Circuit.gateCount circuit)) : Set where
  constructor whole-circuit-placed-meaning
  field
    gateRelations :
      ProgramPlacedGatesValid (Circuit.program circuit) bits
    outputAccepted :
      CNF.lookupBit bits (outputWireFin (Circuit.outputWire circuit))
        ≡ true

wholeCircuitPlacedCNFSound :
  ∀ {inputs : Nat}
    (circuit : Circuit.ConcreteBooleanCircuit inputs)
    (bits : CNF.Bits (inputs + Circuit.gateCount circuit)) →
  CNF.evaluateCNF (circuitPlacedCNF circuit) bits ≡ true →
  WholeCircuitPlacedMeaning circuit bits
wholeCircuitPlacedCNFSound circuit bits accepted =
  whole-circuit-placed-meaning
    (programPlacedCNFSound
      (Circuit.program circuit) bits
      (cnfAndTrueLeft split))
    (trans
      (sym (outputUnitEvaluation circuit bits))
      (CNF.andTrueGivesRight
        (CNF.evaluateCNF
          (programPlacedCNF (Circuit.program circuit)) bits)
        (CNF.evaluateCNF (outputUnitCNF circuit) bits)
        split))
  where
    split :
      CNF.andBool
        (CNF.evaluateCNF
          (programPlacedCNF (Circuit.program circuit)) bits)
        (CNF.evaluateCNF (outputUnitCNF circuit) bits)
      ≡ true
    split =
      trans
        (sym
          (Placed.evaluateCNFAppend
            (programPlacedCNF (Circuit.program circuit))
            (outputUnitCNF circuit) bits))
        accepted

wholeCircuitPlacedCNFComplete :
  ∀ {inputs : Nat}
    (circuit : Circuit.ConcreteBooleanCircuit inputs)
    (bits : CNF.Bits (inputs + Circuit.gateCount circuit)) →
  WholeCircuitPlacedMeaning circuit bits →
  CNF.evaluateCNF (circuitPlacedCNF circuit) bits ≡ true
wholeCircuitPlacedCNFComplete circuit bits
    (whole-circuit-placed-meaning relations accepted) =
  trans
    (Placed.evaluateCNFAppend
      (programPlacedCNF (Circuit.program circuit))
      (outputUnitCNF circuit)
      bits)
    (cnfAndBothTrue
      (programPlacedCNFComplete
        (Circuit.program circuit) bits relations)
      (trans
        (outputUnitEvaluation circuit bits)
        accepted))

-- This soundness/completeness is on the literal whole-circuit CNF and
-- original per-gate relations. The missing stronger bridge remains the
-- equivalence with evaluateProgram on the finite original input vector,
-- which is needed to reuse finiteSupportedTseitinCountExact on THIS CNF.
-- All declarations in this cut are source-written, Agda kernel pending.
