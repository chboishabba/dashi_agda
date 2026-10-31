module DASHI.Research.OpenAIMath.OpenAIMathSharedTseitinOptimizedCNFExact where

------------------------------------------------------------------------
-- Optional 1/2/3-clause specialization of EXISTING same-object DAG 3-CNF.
-- Historical mathematical roots: Cook, Levin, Tseitin (classical).
-- Original source owners: PNotEqualsNPConcreteBooleanCircuitDAGExact and
-- OpenAIMathSharedTseitinGateCNFExact; no replacement core compiler.
-- This uses the SAME variable indices, CNF carrier and semantics.
-- Source-written proof terms, Agda exact-head kernel acceptance PENDING.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Nat.Base using (_≤_; z≤n; s≤s)
import Data.Nat.Properties as NatP
open import Relation.Binary.PropositionalEquality using (cong₂; sym; trans)

import Data.Fin.Base as Fin
import DASHI.Mathematics.Complexity.PNotEqualsNPConcreteBooleanCircuitDAGExact as Circuit
import DASHI.Mathematics.Complexity.FixedWidthTruthTableCNFExact as CNF
import DASHI.Mathematics.Complexity.CNFVariableRenamingExact as Rename
import DASHI.Mathematics.Complexity.CNFPlacedConstraintConjunctionExact as Placed
import DASHI.Mathematics.Complexity.CookLevinGridReplicationExact as Grid
import DASHI.Research.OpenAIMath.OpenAIMathSharedTseitinGateCNFExact as Original

outputIndex : Fin.Fin Original.three
outputIndex = Fin.zero
leftIndex : Fin.Fin Original.three
leftIndex = Fin.suc Fin.zero
rightIndex : Fin.Fin Original.three
rightIndex = Fin.suc (Fin.suc Fin.zero)

optLocalCNF : ∀ {inputs gates : Nat} →
  Circuit.Gate inputs gates → CNF.CNF Original.three
optLocalCNF (Circuit.constantGate false) =
  (CNF.negative outputIndex ∷ []) ∷ []
optLocalCNF (Circuit.constantGate true) =
  (CNF.positive outputIndex ∷ []) ∷ []
optLocalCNF (Circuit.notGate _) =
  (CNF.negative outputIndex ∷ CNF.negative leftIndex ∷ []) ∷
  (CNF.positive outputIndex ∷ CNF.positive leftIndex ∷ []) ∷ []
optLocalCNF (Circuit.andGate _ _) =
  (CNF.negative outputIndex ∷ CNF.positive leftIndex ∷ []) ∷
  (CNF.negative outputIndex ∷ CNF.positive rightIndex ∷ []) ∷
  (CNF.positive outputIndex ∷ CNF.negative leftIndex ∷ CNF.negative rightIndex ∷ []) ∷ []
optLocalCNF (Circuit.orGate _ _) =
  (CNF.positive outputIndex ∷ CNF.negative leftIndex ∷ []) ∷
  (CNF.positive outputIndex ∷ CNF.negative rightIndex ∷ []) ∷
  (CNF.negative outputIndex ∷ CNF.positive leftIndex ∷ CNF.positive rightIndex ∷ []) ∷ []

-- Boolean gate-table validation: all 24 distinct relevant cases.
-- Constant ignores both operands; NOT ignores right operand.
optLocalGateEval : ∀ {inputs gates : Nat}
  (gate : Circuit.Gate inputs gates)
  (out left right : Bool) →
  CNF.evaluateCNF (optLocalCNF gate) (Original.window out left right)
    ≡ Original.localGateConsistent gate (Original.window out left right)
optLocalGateEval (Circuit.constantGate false) false left right = refl
optLocalGateEval (Circuit.constantGate false) true left right = refl
optLocalGateEval (Circuit.constantGate true) false left right = refl
optLocalGateEval (Circuit.constantGate true) true left right = refl
optLocalGateEval (Circuit.notGate source) false false right = refl
optLocalGateEval (Circuit.notGate source) false true right = refl
optLocalGateEval (Circuit.notGate source) true false right = refl
optLocalGateEval (Circuit.notGate source) true true right = refl
optLocalGateEval (Circuit.andGate a b) false false false = refl
optLocalGateEval (Circuit.andGate a b) false false true = refl
optLocalGateEval (Circuit.andGate a b) false true false = refl
optLocalGateEval (Circuit.andGate a b) false true true = refl
optLocalGateEval (Circuit.andGate a b) true false false = refl
optLocalGateEval (Circuit.andGate a b) true false true = refl
optLocalGateEval (Circuit.andGate a b) true true false = refl
optLocalGateEval (Circuit.andGate a b) true true true = refl
optLocalGateEval (Circuit.orGate a b) false false false = refl
optLocalGateEval (Circuit.orGate a b) false false true = refl
optLocalGateEval (Circuit.orGate a b) false true false = refl
optLocalGateEval (Circuit.orGate a b) false true true = refl
optLocalGateEval (Circuit.orGate a b) true false false = refl
optLocalGateEval (Circuit.orGate a b) true false true = refl
optLocalGateEval (Circuit.orGate a b) true true false = refl
optLocalGateEval (Circuit.orGate a b) true true true = refl

optLocalEvalEq : ∀ {inputs gates : Nat}
  (gate : Circuit.Gate inputs gates) (bits : CNF.Bits Original.three) →
  CNF.evaluateCNF (optLocalCNF gate) bits
    ≡ Original.localGateConsistent gate bits
optLocalEvalEq gate (o CNF.∷ᵇ l CNF.∷ᵇ r CNF.∷ᵇ CNF.[]ᵇ) =
  optLocalGateEval gate o l r

optPlacedCNF : ∀ {inputs gates : Nat} →
  Circuit.Gate inputs gates → CNF.CNF (inputs + suc gates)
optPlacedCNF gate =
  Rename.renameCNF (Original.gateWindowRename gate) (optLocalCNF gate)

optPlacedEval : ∀ {inputs gates : Nat}
  (gate : Circuit.Gate inputs gates)
  (bits : CNF.Bits (inputs + suc gates)) →
  CNF.evaluateCNF (optPlacedCNF gate) bits ≡
  Original.localGateConsistent gate
    (Rename.pullbackBits (Original.gateWindowRename gate) bits)
optPlacedEval gate bits =
  trans
    (Rename.renamedCNFEvaluation
      (Original.gateWindowRename gate) (optLocalCNF gate) bits)
    (optLocalEvalEq gate
      (Rename.pullbackBits (Original.gateWindowRename gate) bits))

optPlacedSound : ∀ {inputs gates : Nat}
  (gate : Circuit.Gate inputs gates)
  (bits : CNF.Bits (inputs + suc gates)) →
  CNF.evaluateCNF (optPlacedCNF gate) bits ≡ true →
  Original.localGateConsistent gate
    (Rename.pullbackBits (Original.gateWindowRename gate) bits) ≡ true
optPlacedSound gate bits accepted =
  trans (sym (optPlacedEval gate bits)) accepted

optPlacedComplete : ∀ {inputs gates : Nat}
  (gate : Circuit.Gate inputs gates)
  (bits : CNF.Bits (inputs + suc gates)) →
  Original.localGateConsistent gate
    (Rename.pullbackBits (Original.gateWindowRename gate) bits) ≡ true →
  CNF.evaluateCNF (optPlacedCNF gate) bits ≡ true
optPlacedComplete gate bits accepted =
  trans (optPlacedEval gate bits) accepted

sameBoolean : (left right : Bool) →
  (left ≡ true → right ≡ true) →
  (right ≡ true → left ≡ true) → left ≡ right
sameBoolean false false to fro = refl
sameBoolean false true to fro with fro refl
... | ()
sameBoolean true false to fro with to refl
... | ()
sameBoolean true true to fro = refl

-- Actual Boolean equality with the existing four-clause gate compiler,
-- not merely equality of model counts. Works with repeated/aliased wires.
optPlacedEqualsOriginal : ∀ {inputs gates : Nat}
  (gate : Circuit.Gate inputs gates)
  (bits : CNF.Bits (inputs + suc gates)) →
  CNF.evaluateCNF (optPlacedCNF gate) bits ≡
  CNF.evaluateCNF (Original.placedGateCNF gate) bits
optPlacedEqualsOriginal gate bits =
  sameBoolean _ _
    (λ accepted → Original.placedGateComplete gate bits
      (optPlacedSound gate bits accepted))
    (λ accepted → optPlacedComplete gate bits
      (Original.placedGateSound gate bits accepted))

optProgramCNF : ∀ {inputs gates : Nat} →
  Circuit.GateProgram inputs gates → CNF.CNF (inputs + gates)
optProgramCNF Circuit.noGates = []
optProgramCNF (Circuit.appendGate previous gate) =
  Placed.append
    (Rename.renameCNF Original.extendEarlierFin (optProgramCNF previous))
    (optPlacedCNF gate)

-- Crucial reuse-first result: the optional optimized formula has exactly
-- the same truth value as the ORIGINAL whole program for each assignment.
optProgramEqualsOriginal : ∀ {inputs gates : Nat}
  (program : Circuit.GateProgram inputs gates)
  (bits : CNF.Bits (inputs + gates)) →
  CNF.evaluateCNF (optProgramCNF program) bits ≡
  CNF.evaluateCNF (Original.programPlacedCNF program) bits
optProgramEqualsOriginal Circuit.noGates bits = refl
optProgramEqualsOriginal (Circuit.appendGate previous gate) bits =
  trans
    (Placed.evaluateCNFAppend
      (Rename.renameCNF Original.extendEarlierFin (optProgramCNF previous))
      (optPlacedCNF gate) bits)
    (trans
      (cong₂ CNF.andBool
        (trans
          (Rename.renamedCNFEvaluation
            Original.extendEarlierFin (optProgramCNF previous) bits)
          (trans
            (optProgramEqualsOriginal previous
              (Rename.pullbackBits Original.extendEarlierFin bits))
            (sym
              (Rename.renamedCNFEvaluation
                Original.extendEarlierFin
                (Original.programPlacedCNF previous) bits))))
        (optPlacedEqualsOriginal gate bits))
      (sym
        (Placed.evaluateCNFAppend
          (Rename.renameCNF Original.extendEarlierFin
            (Original.programPlacedCNF previous))
          (Original.placedGateCNF gate) bits))))

optCircuitCNF : ∀ {inputs : Nat} →
  (circuit : Circuit.ConcreteBooleanCircuit inputs) →
  CNF.CNF (inputs + Circuit.gateCount circuit)
optCircuitCNF circuit =
  Placed.append
    (optProgramCNF (Circuit.program circuit))
    (Original.outputUnitCNF circuit)

optCircuitEqualsOriginal : ∀ {inputs : Nat}
  (circuit : Circuit.ConcreteBooleanCircuit inputs)
  (bits : CNF.Bits (inputs + Circuit.gateCount circuit)) →
  CNF.evaluateCNF (optCircuitCNF circuit) bits ≡
  CNF.evaluateCNF (Original.circuitPlacedCNF circuit) bits
optCircuitEqualsOriginal circuit bits =
  trans
    (Placed.evaluateCNFAppend
      (optProgramCNF (Circuit.program circuit))
      (Original.outputUnitCNF circuit) bits)
    (trans
      (cong₂ CNF.andBool
        (optProgramEqualsOriginal (Circuit.program circuit) bits)
        refl)
      (sym
        (Placed.evaluateCNFAppend
          (Original.programPlacedCNF (Circuit.program circuit))
          (Original.outputUnitCNF circuit) bits)))

optCircuitSound : ∀ {inputs : Nat}
  (circuit : Circuit.ConcreteBooleanCircuit inputs)
  (bits : CNF.Bits (inputs + Circuit.gateCount circuit)) →
  CNF.evaluateCNF (optCircuitCNF circuit) bits ≡ true →
  Original.WholeCircuitPlacedMeaning circuit bits
optCircuitSound circuit bits accepted =
  Original.wholeCircuitPlacedCNFSound circuit bits
    (trans (sym (optCircuitEqualsOriginal circuit bits)) accepted)

optCircuitComplete : ∀ {inputs : Nat}
  (circuit : Circuit.ConcreteBooleanCircuit inputs)
  (bits : CNF.Bits (inputs + Circuit.gateCount circuit)) →
  Original.WholeCircuitPlacedMeaning circuit bits →
  CNF.evaluateCNF (optCircuitCNF circuit) bits ≡ true
optCircuitComplete circuit bits meaning =
  trans (optCircuitEqualsOriginal circuit bits)
    (Original.wholeCircuitPlacedCNFComplete circuit bits meaning)

optGateClauseCost : ∀ {inputs gates : Nat} → Circuit.Gate inputs gates → Nat
optGateClauseCost (Circuit.constantGate _) = 1
optGateClauseCost (Circuit.notGate _) = 2
optGateClauseCost (Circuit.andGate _ _) = 3
optGateClauseCost (Circuit.orGate _ _) = 3

optLocalClauseCount : ∀ {inputs gates : Nat}
  (gate : Circuit.Gate inputs gates) →
  Grid.listLength (optLocalCNF gate) ≡ optGateClauseCost gate
optLocalClauseCount (Circuit.constantGate false) = refl
optLocalClauseCount (Circuit.constantGate true) = refl
optLocalClauseCount (Circuit.notGate _) = refl
optLocalClauseCount (Circuit.andGate _ _) = refl
optLocalClauseCount (Circuit.orGate _ _) = refl

optPlacedClauseCount : ∀ {inputs gates : Nat}
  (gate : Circuit.Gate inputs gates) →
  Grid.listLength (optPlacedCNF gate) ≡ optGateClauseCost gate
optPlacedClauseCount gate =
  trans
    (Original.renameCNFClauseCountExact
      (Original.gateWindowRename gate) (optLocalCNF gate))
    (optLocalClauseCount gate)

optProgramCost : ∀ {inputs gates : Nat} →
  Circuit.GateProgram inputs gates → Nat
optProgramCost Circuit.noGates = zero
optProgramCost (Circuit.appendGate previous gate) =
  optProgramCost previous + optGateClauseCost gate

optProgramClauseCount : ∀ {inputs gates : Nat}
  (program : Circuit.GateProgram inputs gates) →
  Grid.listLength (optProgramCNF program) ≡ optProgramCost program
optProgramClauseCount Circuit.noGates = refl
optProgramClauseCount (Circuit.appendGate previous gate) =
  trans
    (Original.placedAppendLength
      (Rename.renameCNF Original.extendEarlierFin (optProgramCNF previous))
      (optPlacedCNF gate))
    (cong₂ _+_
      (trans
        (Original.renameCNFClauseCountExact
          Original.extendEarlierFin (optProgramCNF previous))
        (optProgramClauseCount previous))
      (optPlacedClauseCount gate))

optCircuitClauseCount : ∀ {inputs : Nat}
  (circuit : Circuit.ConcreteBooleanCircuit inputs) →
  Grid.listLength (optCircuitCNF circuit)
    ≡ optProgramCost (Circuit.program circuit) + suc zero
optCircuitClauseCount circuit =
  trans
    (Original.placedAppendLength
      (optProgramCNF (Circuit.program circuit))
      (Original.outputUnitCNF circuit))
    (cong₂ _+_
      (optProgramClauseCount (Circuit.program circuit))
      (Original.outputUnitCNFClauseCount circuit))

-- Cost = 1 per constant, 2 per NOT, 3 per AND/OR, +1 output.
-- Original fixed-width truth-table implementation uses 4 per gate +1.
-- The original theorem remains intact. List counts are NOT Finset.card.
-- No claimed ETH/P=NP or general Max-Cut speedup.


------------------------------------------------------------------------
-- A UNIFORM SOURCE-CLAUSE BUDGET: <= 3*g+1 for any concrete original DAG.
-- The numeric bound is a Nat theorem about literal source clause LISTS;
-- the upstream deduplicated Finset.card can be smaller.
------------------------------------------------------------------------

optGateCostAtMostThree : ∀ {inputs gates : Nat}
  (gate : Circuit.Gate inputs gates) → optGateClauseCost gate ≤ 3
optGateCostAtMostThree (Circuit.constantGate _) = s≤s z≤n
optGateCostAtMostThree (Circuit.notGate _) = s≤s (s≤s z≤n)
optGateCostAtMostThree (Circuit.andGate _ _) =
  s≤s (s≤s (s≤s z≤n))
optGateCostAtMostThree (Circuit.orGate _ _) =
  s≤s (s≤s (s≤s z≤n))

threePerGate : Nat → Nat
threePerGate zero = zero
threePerGate (suc gates) = threePerGate gates + 3

optProgramLeThreePerGate : ∀ {inputs gates : Nat}
  (program : Circuit.GateProgram inputs gates) →
  optProgramCost program ≤ threePerGate gates
optProgramLeThreePerGate Circuit.noGates = z≤n
optProgramLeThreePerGate (Circuit.appendGate previous gate) =
  NatP.+-mono-≤
    (optProgramLeThreePerGate previous)
    (optGateCostAtMostThree gate)

optCircuitThreeClauseBudget : ∀ {inputs : Nat}
  (circuit : Circuit.ConcreteBooleanCircuit inputs) →
  Grid.listLength (optCircuitCNF circuit)
    ≤ threePerGate (Circuit.gateCount circuit) + suc zero
optCircuitThreeClauseBudget circuit =
  NatP.≤-trans
    (NatP.≤-reflexive (optCircuitClauseCount circuit))
    (NatP.+-mono-≤
      (optProgramLeThreePerGate (Circuit.program circuit))
      (s≤s z≤n))

-- Multiplication is a closed-form restatement of structural threePerGate.
-- Unlike the original four-clause template, no truth table is expanded
-- over the full original input dimension.


------------------------------------------------------------------------
-- EXACT NUMERIC #SAT EQUIVALENCE FOR THE TWO WHOLE CNF COMPILERS.
-- Uses the EXISTING pointwise proof above. No new gate-evaluation engine,
-- no oracle, no unbounded Nat -> Bool assignment, no new compiler.
------------------------------------------------------------------------

indicator : Bool → Nat
indicator false = zero
indicator true = suc zero

-- Entirely finite global CNF assignment carrier, not Cook.Assignment.
sumFiniteBits : ∀ {n : Nat} → (CNF.Bits n → Nat) → Nat
sumFiniteBits {zero} weight = weight CNF.[]ᵇ
sumFiniteBits {suc n} weight =
  sumFiniteBits (λ bits → weight (false CNF.∷ᵇ bits)) +
  sumFiniteBits (λ bits → weight (true CNF.∷ᵇ bits))

sumFiniteBitsExt : ∀ {n : Nat}
  (left right : CNF.Bits n → Nat) →
  ((bits : CNF.Bits n) → left bits ≡ right bits) →
  sumFiniteBits left ≡ sumFiniteBits right
sumFiniteBitsExt {zero} left right equality =
  equality CNF.[]ᵇ
sumFiniteBitsExt {suc n} left right equality =
  cong₂ _+_
    (sumFiniteBitsExt
      (λ bits → left (false CNF.∷ᵇ bits))
      (λ bits → right (false CNF.∷ᵇ bits))
      (λ bits → equality (false CNF.∷ᵇ bits)))
    (sumFiniteBitsExt
      (λ bits → left (true CNF.∷ᵇ bits))
      (λ bits → right (true CNF.∷ᵇ bits))
      (λ bits → equality (true CNF.∷ᵇ bits)))

countSourceCNF : ∀ {n : Nat} → CNF.CNF n → Nat
countSourceCNF formula =
  sumFiniteBits (λ bits → indicator (CNF.evaluateCNF formula bits))

optCircuitCountEqualsOriginal : ∀ {inputs : Nat}
  (circuit : Circuit.ConcreteBooleanCircuit inputs) →
  countSourceCNF (optCircuitCNF circuit) ≡
    countSourceCNF (Original.circuitPlacedCNF circuit)
optCircuitCountEqualsOriginal circuit =
  sumFiniteBitsExt
    (λ bits → indicator (CNF.evaluateCNF (optCircuitCNF circuit) bits))
    (λ bits → indicator (CNF.evaluateCNF (Original.circuitPlacedCNF circuit) bits))
    (λ bits → cong-indicator (optCircuitEqualsOriginal circuit bits))
  where
    cong-indicator : ∀ {left right : Bool} →
      left ≡ right → indicator left ≡ indicator right
    cong-indicator refl = refl

-- **Paid only at source level**: same finite assignment domain and exactly
-- equal computed Nat counts for optimized vs original full source CNFs.
-- NOT yet the stronger equation with original accepted Circuit input count;
-- that demands original finite-gate-value normalization, and any cross-
-- language Finset conversion needs separate semantics + cardinality proof.


------------------------------------------------------------------------
-- FORMAL NORMALIZATION GENERATORS FOR FUTURE AGDA-LIST -> LEAN-FINSET
-- TRANSPORT. All are proved on the ORIGINAL CNF Boolean semantics:
-- duplicate elimination, adjacent permutations, tautological clauses.
-- They do not yet construct or import Lean's Finset quotient.
------------------------------------------------------------------------

cnfOrSwap : (a b c : Bool) →
  CNF.orBool a (CNF.orBool b c) ≡
    CNF.orBool b (CNF.orBool a c)
cnfOrSwap false false c = refl
cnfOrSwap false true c = refl
cnfOrSwap true false c = refl
cnfOrSwap true true c = refl

cnfAndSwap : (a b c : Bool) →
  CNF.andBool a (CNF.andBool b c) ≡
    CNF.andBool b (CNF.andBool a c)
cnfAndSwap false false c = refl
cnfAndSwap false true c = refl
cnfAndSwap true false c = refl
cnfAndSwap true true c = refl

duplicateLiteralPreserves :
  ∀ {n : Nat}
    (literal : CNF.Literal n)
    (tail : CNF.Clause n)
    (bits : CNF.Bits n) →
  CNF.evaluateClause (literal ∷ literal ∷ tail) bits ≡
    CNF.evaluateClause (literal ∷ tail) bits
duplicateLiteralPreserves literal tail bits
  with CNF.evaluateLiteral literal bits
... | false = refl
... | true = refl

duplicateClausePreserves :
  ∀ {n : Nat}
    (clause : CNF.Clause n)
    (tail : CNF.CNF n)
    (bits : CNF.Bits n) →
  CNF.evaluateCNF (clause ∷ clause ∷ tail) bits ≡
    CNF.evaluateCNF (clause ∷ tail) bits
duplicateClausePreserves clause tail bits
  with CNF.evaluateClause clause bits
... | false = refl
... | true = refl

swapAdjacentLiteralsPreserves :
  ∀ {n : Nat}
    (left right : CNF.Literal n)
    (tail : CNF.Clause n)
    (bits : CNF.Bits n) →
  CNF.evaluateClause (left ∷ right ∷ tail) bits ≡
    CNF.evaluateClause (right ∷ left ∷ tail) bits
swapAdjacentLiteralsPreserves left right tail bits =
  cnfOrSwap
    (CNF.evaluateLiteral left bits)
    (CNF.evaluateLiteral right bits)
    (CNF.evaluateClause tail bits)

swapAdjacentClausesPreserves :
  ∀ {n : Nat}
    (left right : CNF.Clause n)
    (tail : CNF.CNF n)
    (bits : CNF.Bits n) →
  CNF.evaluateCNF (left ∷ right ∷ tail) bits ≡
    CNF.evaluateCNF (right ∷ left ∷ tail) bits
swapAdjacentClausesPreserves left right tail bits =
  cnfAndSwap
    (CNF.evaluateClause left bits)
    (CNF.evaluateClause right bits)
    (CNF.evaluateCNF tail bits)

tautologicalClauseTrue :
  ∀ {n : Nat}
    (variable : Fin.Fin n)
    (tail : CNF.Clause n)
    (bits : CNF.Bits n) →
  CNF.evaluateClause
    (CNF.positive variable ∷ CNF.negative variable ∷ tail)
    bits ≡ true
tautologicalClauseTrue variable tail bits
  with CNF.lookupBit bits variable
... | false = refl
... | true = refl

-- These six source-level lemmas show CNF semantics is invariant under
-- the elementary equality generators of finite literal/clause SETS.
-- Full Agda->Lean Finset normalization (especially finite cardinal bounds,
-- compiler/machine costs, and kernel receipt) remains explicitly unpaid.


------------------------------------------------------------------------
-- Transport CNF normalization through the finite numeric #SAT COUNT.
-- This is strictly stronger than Boolean equisatisfiability: it states
-- equality of the actual number of supported finite assignments.
------------------------------------------------------------------------

countFromPointwise : ∀ {n : Nat}
  (left right : CNF.CNF n) →
  ((bits : CNF.Bits n) →
    CNF.evaluateCNF left bits ≡ CNF.evaluateCNF right bits) →
  countSourceCNF left ≡ countSourceCNF right
countFromPointwise left right pointwise =
  sumFiniteBitsExt
    (λ bits → indicator (CNF.evaluateCNF left bits))
    (λ bits → indicator (CNF.evaluateCNF right bits))
    (λ bits → cong-indicator (pointwise bits))
  where
    cong-indicator : ∀ {a b : Bool} →
      a ≡ b → indicator a ≡ indicator b
    cong-indicator refl = refl

duplicateClauseCountInvariant : ∀ {n : Nat}
  (clause : CNF.Clause n) (tail : CNF.CNF n) →
  countSourceCNF (clause ∷ clause ∷ tail) ≡
    countSourceCNF (clause ∷ tail)
duplicateClauseCountInvariant clause tail =
  countFromPointwise (clause ∷ clause ∷ tail)
    (clause ∷ tail)
    (duplicateClausePreserves clause tail)

swapClauseCountInvariant : ∀ {n : Nat}
  (left right : CNF.Clause n) (tail : CNF.CNF n) →
  countSourceCNF (left ∷ right ∷ tail) ≡
    countSourceCNF (right ∷ left ∷ tail)
swapClauseCountInvariant left right tail =
  countFromPointwise
    (left ∷ right ∷ tail)
    (right ∷ left ∷ tail)
    (swapAdjacentClausesPreserves left right tail)

tautologyRemovesFromCNF : ∀ {n : Nat}
  (variable : Fin.Fin n)
  (clauseTail : CNF.Clause n)
  (remaining : CNF.CNF n)
  (bits : CNF.Bits n) →
  CNF.evaluateCNF
    ((CNF.positive variable ∷ CNF.negative variable ∷ clauseTail) ∷ remaining)
    bits ≡ CNF.evaluateCNF remaining bits
tautologyRemovesFromCNF variable clauseTail remaining bits
  rewrite tautologicalClauseTrue variable clauseTail bits = refl

tautologyRemovalCountInvariant : ∀ {n : Nat}
  (variable : Fin.Fin n)
  (clauseTail : CNF.Clause n)
  (remaining : CNF.CNF n) →
  countSourceCNF
    ((CNF.positive variable ∷ CNF.negative variable ∷ clauseTail) ∷ remaining)
    ≡ countSourceCNF remaining
tautologyRemovalCountInvariant variable clauseTail remaining =
  countFromPointwise
    ((CNF.positive variable ∷ CNF.negative variable ∷ clauseTail) ∷ remaining)
    remaining
    (tautologyRemovesFromCNF variable clauseTail remaining)

duplicateLiteralCountInvariant : ∀ {n : Nat}
  (literal : CNF.Literal n)
  (restClause : CNF.Clause n)
  (restFormula : CNF.CNF n) →
  countSourceCNF ((literal ∷ literal ∷ restClause) ∷ restFormula) ≡
    countSourceCNF ((literal ∷ restClause) ∷ restFormula)
duplicateLiteralCountInvariant literal restClause restFormula =
  countFromPointwise
    ((literal ∷ literal ∷ restClause) ∷ restFormula)
    ((literal ∷ restClause) ∷ restFormula)
    (λ bits →
      cong₂ CNF.andBool
        (duplicateLiteralPreserves literal restClause bits)
        refl)

-- These are the exact same-assignment cardinality laws needed to justify
-- clause/literal dedup and tautology deletion on the future Lean Finset
-- conversion. Finset construction and the upstream machine theorem remain
-- separate, not silently proved here. Kernel acceptance remains pending.
