module DASHI.Mathematics.Complexity.ConcreteTapeEndpointCNFExact where

------------------------------------------------------------------------
-- POLYNOMIAL ENDPOINT CNFs OVER AN EXTENDED GLOBAL TRACE VECTOR
--
-- Base trace bits:
--   [ rows ][ transition rule selectors ]
--
-- Endpoint extension:
--   [ base trace ][ final-row acceptance witnesses ]
--
-- Initial endpoint:
--   row_0 is fixed by one unit clause per target bit.
--
-- Accepting endpoint:
--   one witness bit per final-row cell;
--   (1) one big clause requires some witness;
--   (2) for each cell, witness -> decoded cell has headed accepting state.
--
-- The implication predicate has constant local width
--   1 + CellWidth,
-- so its truth-table CNF is machine-dependent constant size and replication
-- over columns is polynomial.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
import Data.Fin.Base as Fin

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeCanonicalCellBitsExact as Canonical
import DASHI.Mathematics.Complexity.ConcreteTapeFixedDimensionDecodeExact as Decode
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalTraceDecodeExact as Trace
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalTracePlacementExact as Global
import DASHI.Mathematics.Complexity.ConcreteTapeCanonicalWindowPlacementExact as Placement
import DASHI.Mathematics.Complexity.CNFVariableRenamingExact as Rename
import DASHI.Mathematics.Complexity.CNFPlacedConstraintConjunctionExact as Placed
import DASHI.Mathematics.Complexity.FixedWidthTruthTableCNFExact as CNF

ExtendedGlobalWidth :
  Local.ConcreteTapeMachine → Nat → Nat → Nat
ExtendedGlobalWidth machine steps cols =
  Trace.GlobalTraceWidth machine steps cols + cols

liftBaseIndex :
  ∀ {machine steps cols} →
  Fin.Fin (Trace.GlobalTraceWidth machine steps cols) →
  Fin.Fin (ExtendedGlobalWidth machine steps cols)
liftBaseIndex = Placement.finLeft

witnessIndex :
  ∀ {machine steps cols} →
  Fin.Fin cols →
  Fin.Fin (ExtendedGlobalWidth machine steps cols)
witnessIndex {machine} {steps} {cols} =
  Placement.finRight (Trace.GlobalTraceWidth machine steps cols)

------------------------------------------------------------------------
-- Exact target-bit endpoint CNF
------------------------------------------------------------------------

unitClauseForBit :
  ∀ {global} →
  Fin.Fin global →
  Bool →
  CNF.Clause global
unitClauseForBit index false =
  CNF.negative index ∷ []
unitClauseForBit index true =
  CNF.positive index ∷ []

unitClausesForTarget :
  ∀ {local global} →
  (Fin.Fin local → Fin.Fin global) →
  CNF.Bits local →
  CNF.CNF global
unitClausesForTarget rename CNF.[]ᵇ = []
unitClausesForTarget rename (bit CNF.∷ᵇ bits) =
  unitClauseForBit (rename Fin.zero) bit
  ∷
  unitClausesForTarget
    (λ i → rename (Fin.suc i))
    bits

unitClausesForTarget_complete :
  ∀ {local global}
    (rename : Fin.Fin local → Fin.Fin global)
    (target : CNF.Bits local)
    (assignment : CNF.Bits global) →
  Rename.pullbackBits rename assignment ≡ target →
  CNF.evaluateCNF
    (unitClausesForTarget rename target)
    assignment
  ≡ true
unitClausesForTarget_complete rename CNF.[]ᵇ assignment proof =
  refl
unitClausesForTarget_complete
    rename (false CNF.∷ᵇ target) assignment proof
    with congr (λ bits → CNF.lookupBit bits Fin.zero) proof
... | headEq
    with Rename.pullbackLookup rename assignment Fin.zero
... | lookupEq
    rewrite lookupEq | headEq =
  unitClausesForTarget_complete
    (λ i → rename (Fin.suc i))
    target assignment
    (tailEq proof)
  where
    tailBits : ∀ {n} → CNF.Bits (suc n) → CNF.Bits n
    tailBits (b CNF.∷ᵇ bs) = bs

    tailEq :
      ∀ {n} {x y : CNF.Bits (suc n)} →
      x ≡ y → tailBits x ≡ tailBits y
    tailEq refl = refl
unitClausesForTarget_complete
    rename (true CNF.∷ᵇ target) assignment proof
    with congr (λ bits → CNF.lookupBit bits Fin.zero) proof
... | headEq
    with Rename.pullbackLookup rename assignment Fin.zero
... | lookupEq
    rewrite lookupEq | headEq =
  unitClausesForTarget_complete
    (λ i → rename (Fin.suc i))
    target assignment
    (tailEq proof)
  where
    tailBits : ∀ {n} → CNF.Bits (suc n) → CNF.Bits n
    tailBits (b CNF.∷ᵇ bs) = bs

    tailEq :
      ∀ {n} {x y : CNF.Bits (suc n)} →
      x ≡ y → tailBits x ≡ tailBits y
    tailEq refl = refl

initialRowExtendedRename :
  ∀ {machine steps cols} →
  Fin.Fin (Decode.RowBitsWidth machine cols) →
  Fin.Fin (ExtendedGlobalWidth machine steps cols)
initialRowExtendedRename i =
  liftBaseIndex
    (Global.globalRowRename Global.here i)

initialEndpointCNF :
  ∀ {machine steps cols} →
  CNF.Bits (Decode.RowBitsWidth machine cols) →
  CNF.CNF (ExtendedGlobalWidth machine steps cols)
initialEndpointCNF target =
  unitClausesForTarget initialRowExtendedRename target

------------------------------------------------------------------------
-- Acceptance witness clause
------------------------------------------------------------------------

allWitnessPositiveLiterals :
  ∀ {machine steps cols} →
  (Fin.Fin cols → CNF.Literal (ExtendedGlobalWidth machine steps cols)) →
  List (Fin.Fin cols) →
  CNF.Clause (ExtendedGlobalWidth machine steps cols)
allWitnessPositiveLiterals literal [] = []
allWitnessPositiveLiterals literal (i ∷ rest) =
  literal i ∷ allWitnessPositiveLiterals literal rest

finList :
  (n : Nat) → List (Fin.Fin n)
finList zero = []
finList (suc n) =
  Fin.zero ∷ mapSuc (finList n)
  where
    mapSuc : ∀ {m} → List (Fin.Fin m) → List (Fin.Fin (suc m))
    mapSuc [] = []
    mapSuc (i ∷ rest) = Fin.suc i ∷ mapSuc rest

someAcceptanceWitnessClause :
  ∀ {machine steps cols} →
  CNF.Clause (ExtendedGlobalWidth machine steps cols)
someAcceptanceWitnessClause {machine} {steps} {cols} =
  allWitnessPositiveLiterals
    (λ i → CNF.positive (witnessIndex i))
    (finList cols)

------------------------------------------------------------------------
-- Local witness -> decoded accepting cell
------------------------------------------------------------------------

AcceptanceLocalWidth :
  Local.ConcreteTapeMachine → Nat
AcceptanceLocalWidth machine =
  suc (Canonical.CellWidth machine)

cellDecodedAccepting :
  ∀ {machine}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine)) →
  CNF.Bits (Canonical.CellWidth machine) →
  Bool
cellDecodedAccepting {machine} stateCoverage symbolCoverage bits
    with Canonical.decodeCell stateCoverage symbolCoverage bits
... | Local.plain symbol = false
... | Local.headed state symbol =
  Local.decideEqual (Local.finiteState machine)
    state (Local.acceptingState machine)

witnessAcceptingPredicate :
  ∀ {machine}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine)) →
  CNF.Bits (AcceptanceLocalWidth machine) →
  Bool
witnessAcceptingPredicate stateCoverage symbolCoverage
    (false CNF.∷ᵇ cellBits) =
  true
witnessAcceptingPredicate stateCoverage symbolCoverage
    (true CNF.∷ᵇ cellBits) =
  cellDecodedAccepting stateCoverage symbolCoverage cellBits

finalRowSlot :
  ∀ (steps : Nat) →
  Global.Slot steps (suc steps)
finalRowSlot zero = Global.here
finalRowSlot (suc steps) =
  Global.there (finalRowSlot steps)

acceptanceLocalRename :
  ∀ {machine steps cols cellIndex} →
  Global.Slot cellIndex cols →
  Fin.Fin (AcceptanceLocalWidth machine) →
  Fin.Fin (ExtendedGlobalWidth machine steps cols)
acceptanceLocalRename {machine} {steps} {cols} cellSlot Fin.zero =
  witnessIndex (slotToFin cellSlot)
  where
    slotToFin :
      ∀ {i n} → Global.Slot i n → Fin.Fin n
    slotToFin Global.here = Fin.zero
    slotToFin (Global.there s) = Fin.suc (slotToFin s)
acceptanceLocalRename {machine} {steps} {cols} cellSlot (Fin.suc i) =
  liftBaseIndex
    (Global.globalRowRename
      (finalRowSlot steps)
      (Global.blockRename cellSlot i))

acceptancePlacedPredicate :
  ∀ {machine steps cols cellIndex}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (cellSlot : Global.Slot cellIndex cols) →
  Placed.PlacedPredicate
    (AcceptanceLocalWidth machine)
    (ExtendedGlobalWidth machine steps cols)
acceptancePlacedPredicate
    stateCoverage symbolCoverage cellSlot =
  Placed.placed-predicate
    (acceptanceLocalRename cellSlot)
    (witnessAcceptingPredicate
      stateCoverage symbolCoverage)

acceptanceImplicationPredicates :
  ∀ {machine steps cols}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine)) →
  List (Global.SomeSlot cols) →
  List
    (Placed.PlacedPredicate
      (AcceptanceLocalWidth machine)
      (ExtendedGlobalWidth machine steps cols))
acceptanceImplicationPredicates stateCoverage symbolCoverage [] = []
acceptanceImplicationPredicates stateCoverage symbolCoverage
    (Global.some-slot index slot ∷ rest) =
  acceptancePlacedPredicate stateCoverage symbolCoverage slot
  ∷ acceptanceImplicationPredicates
      stateCoverage symbolCoverage rest

appendCNF :
  ∀ {n} → CNF.CNF n → CNF.CNF n → CNF.CNF n
appendCNF = Placed.append

acceptingEndpointCNF :
  ∀ {machine steps cols}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine)) →
  CNF.CNF (ExtendedGlobalWidth machine steps cols)
acceptingEndpointCNF stateCoverage symbolCoverage =
  someAcceptanceWitnessClause
  ∷
  Placed.compilePlacedAll
    (acceptanceImplicationPredicates
      stateCoverage symbolCoverage
      (Global.allSlots _))

record EndpointCNFReceipt
    (machine : Local.ConcreteTapeMachine) : Set₁ where
  field
    initialUnitClauseCompilerPaid : Bool
    initialUnitClauseCompletenessPaid : Bool
    acceptanceWitnessBitsPaid : Bool
    acceptanceExistenceClausePaid : Bool
    witnessImpliesDecodedAcceptingCellPaid : Bool
    constantLocalAcceptanceCNFPaid : Bool
    allFinalCellsPlacementPaid : Bool
    polynomialEndpointShapePaid : Bool
    endpointSoundCompletePaid : Bool
    globalFormulaAssemblyPaid : Bool
    acceptingAssignmentIffRunPaid : Bool
    polynomialReductionPaid : Bool
    pVsNPResolved : Bool

endpointCNFReceipt :
  ∀ (machine : Local.ConcreteTapeMachine) →
  EndpointCNFReceipt machine
endpointCNFReceipt machine = record
  { initialUnitClauseCompilerPaid = true
  ; initialUnitClauseCompletenessPaid = true
  ; acceptanceWitnessBitsPaid = true
  ; acceptanceExistenceClausePaid = true
  ; witnessImpliesDecodedAcceptingCellPaid = true
  ; constantLocalAcceptanceCNFPaid = true
  ; allFinalCellsPlacementPaid = true
  ; polynomialEndpointShapePaid = true
  ; endpointSoundCompletePaid = false
  ; globalFormulaAssemblyPaid = false
  ; acceptingAssignmentIffRunPaid = false
  ; polynomialReductionPaid = false
  ; pVsNPResolved = false
  }
