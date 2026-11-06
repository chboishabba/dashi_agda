module DASHI.Mathematics.Complexity.ConcreteTapeCanonicalEndcapCNFExact where

------------------------------------------------------------------------
-- ORIGINAL CANONICAL CELL BITS -> TRUE PLAIN ENDCAP CNF.
--
-- The first bit of the existing CellWidth code literally selects the
-- Local.plain / Local.headed constructor. This file compiles the
-- true decoded-cell endcap predicate through the existing fixed-width
-- truth-table CNF and arbitrary Fin placement; no new cell codec,
-- witness oracle, or altered SAT language is introduced.
--
-- This pays a SINGLE positioned cell. The remaining owner must
-- enumerate the two physical endcaps for every actual decoded row,
-- prove rowSlice / cell-block correspondence and conjoin the result
-- to the canonical global Cook--Levin CNF. The theorem below does
-- not claim those global operations are already compiled.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (trans; cong₂)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
import Data.Fin.Base as Fin

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeCanonicalCellBitsExact as Canonical
import DASHI.Mathematics.Complexity.ConcreteTapeLocalWindowPatternsExact as Pattern
import DASHI.Mathematics.Complexity.FixedWidthTruthTableCNFExact as CNF
import DASHI.Mathematics.Complexity.CNFVariableRenamingExact as Rename
import DASHI.Mathematics.Complexity.CNFPlacedConstraintConjunctionExact as Placed
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalTracePlacementExact as Global
import DASHI.Mathematics.Complexity.ConcreteTapeEndpointCNFExact as Endpoint

-- The tag is the first bit of the original actual canonical cell block.
-- A headed cell is rejected independently of its arbitrary state/symbol
-- payload, including noncanonical one-hot values.
plainEndcapPredicate :
  ∀ {machine : Local.ConcreteTapeMachine} →
  CNF.Bits (Canonical.CellWidth machine) → Bool
plainEndcapPredicate (false CNF.∷ᵇ payload) = true
plainEndcapPredicate (true CNF.∷ᵇ payload) = false

plainEndcapPredicateSound :
  ∀ {machine}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (cellBits : CNF.Bits (Canonical.CellWidth machine)) →
  plainEndcapPredicate cellBits ≡ true →
  Pattern.IsPlainCell
    (Canonical.decodeCell stateCoverage symbolCoverage cellBits)
plainEndcapPredicateSound stateCoverage symbolCoverage
    (false CNF.∷ᵇ payload) proof = Pattern.is-plain
plainEndcapPredicateSound stateCoverage symbolCoverage
    (true CNF.∷ᵇ payload) ()

plainEndcapPredicateComplete :
  ∀ {machine}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (cellBits : CNF.Bits (Canonical.CellWidth machine)) →
  Pattern.IsPlainCell
    (Canonical.decodeCell stateCoverage symbolCoverage cellBits) →
  plainEndcapPredicate cellBits ≡ true
plainEndcapPredicateComplete stateCoverage symbolCoverage
    (false CNF.∷ᵇ payload) Pattern.is-plain = refl
plainEndcapPredicateComplete stateCoverage symbolCoverage
    (true CNF.∷ᵇ payload) ()

canonicalPlainEndcapCNF :
  ∀ {machine : Local.ConcreteTapeMachine} →
  CNF.CNF (Canonical.CellWidth machine)
canonicalPlainEndcapCNF =
  CNF.truthTableCNF plainEndcapPredicate

canonicalPlainEndcapCNFSound :
  ∀ {machine}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (cellBits : CNF.Bits (Canonical.CellWidth machine)) →
  CNF.evaluateCNF canonicalPlainEndcapCNF cellBits ≡ true →
  Pattern.IsPlainCell
    (Canonical.decodeCell stateCoverage symbolCoverage cellBits)
canonicalPlainEndcapCNFSound stateCoverage symbolCoverage cellBits accepted =
  plainEndcapPredicateSound stateCoverage symbolCoverage cellBits
    (CNF.truthTableCNFSound plainEndcapPredicate cellBits accepted)

canonicalPlainEndcapCNFComplete :
  ∀ {machine}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (cellBits : CNF.Bits (Canonical.CellWidth machine)) →
  Pattern.IsPlainCell
    (Canonical.decodeCell stateCoverage symbolCoverage cellBits) →
  CNF.evaluateCNF canonicalPlainEndcapCNF cellBits ≡ true
canonicalPlainEndcapCNFComplete stateCoverage symbolCoverage cellBits plain =
  CNF.truthTableCNFComplete plainEndcapPredicate cellBits
    (plainEndcapPredicateComplete stateCoverage symbolCoverage cellBits plain)

-- Arbitrary original Fin placement into the same global assignment.
placedPlainEndcapCNF :
  ∀ {machine : Local.ConcreteTapeMachine} {global}
    (rename :
      Fin.Fin (Canonical.CellWidth machine) → Fin.Fin global) →
  CNF.CNF global
placedPlainEndcapCNF rename =
  Rename.renameCNF rename canonicalPlainEndcapCNF

placedPlainEndcapSound :
  ∀ {machine global}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (rename :
      Fin.Fin (Canonical.CellWidth machine) → Fin.Fin global)
    (assignment : CNF.Bits global) →
  CNF.evaluateCNF (placedPlainEndcapCNF rename) assignment ≡ true →
  Pattern.IsPlainCell
    (Canonical.decodeCell stateCoverage symbolCoverage
      (Rename.pullbackBits rename assignment))
placedPlainEndcapSound stateCoverage symbolCoverage
    rename assignment accepted =
  plainEndcapPredicateSound stateCoverage symbolCoverage
    (Rename.pullbackBits rename assignment)
    (Rename.placedTruthTableCNFSound
      rename plainEndcapPredicate assignment accepted)

placedPlainEndcapComplete :
  ∀ {machine global}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (rename :
      Fin.Fin (Canonical.CellWidth machine) → Fin.Fin global)
    (assignment : CNF.Bits global) →
  Pattern.IsPlainCell
    (Canonical.decodeCell stateCoverage symbolCoverage
      (Rename.pullbackBits rename assignment)) →
  CNF.evaluateCNF (placedPlainEndcapCNF rename) assignment ≡ true
placedPlainEndcapComplete stateCoverage symbolCoverage
    rename assignment plain =
  Rename.placedTruthTableCNFComplete
    rename plainEndcapPredicate assignment
    (plainEndcapPredicateComplete stateCoverage symbolCoverage
      (Rename.pullbackBits rename assignment) plain)

------------------------------------------------------------------------
-- SAME ORIGINAL GLOBAL SAT ASSIGNMENT: ROW/COLUMN BLOCK PLACEMENT.
--
-- The actual endcap cell is selected by Global.globalRowRename,
-- Global.blockRename, and Endpoint.liftBaseIndex. This neither
-- introduces fresh bits nor duplicates row codecs. A per-row
-- conjunction producer can reuse this compiled canonical predicate.
------------------------------------------------------------------------

rowCellExtendedRename :
  ∀ {machine steps cols rowIndex colIndex} →
  Global.Slot rowIndex (suc steps) →
  Global.Slot colIndex cols →
  Fin.Fin (Canonical.CellWidth machine) →
  Fin.Fin (Endpoint.ExtendedGlobalWidth machine steps cols)
rowCellExtendedRename rowSlot cellSlot index =
  Endpoint.liftBaseIndex
    (Global.globalRowRename rowSlot
      (Global.blockRename cellSlot index))

globalRowCellPlainCNF :
  ∀ {machine steps cols rowIndex colIndex} →
  Global.Slot rowIndex (suc steps) →
  Global.Slot colIndex cols →
  CNF.CNF (Endpoint.ExtendedGlobalWidth machine steps cols)
globalRowCellPlainCNF rowSlot cellSlot =
  placedPlainEndcapCNF (rowCellExtendedRename rowSlot cellSlot)

globalRowCellPlainSound :
  ∀ {machine steps cols rowIndex colIndex}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (rowSlot : Global.Slot rowIndex (suc steps))
    (cellSlot : Global.Slot colIndex cols)
    (assignment :
      CNF.Bits (Endpoint.ExtendedGlobalWidth machine steps cols)) →
  CNF.evaluateCNF
    (globalRowCellPlainCNF rowSlot cellSlot) assignment ≡ true →
  Pattern.IsPlainCell
    (Canonical.decodeCell stateCoverage symbolCoverage
      (Rename.pullbackBits
        (rowCellExtendedRename rowSlot cellSlot) assignment))
globalRowCellPlainSound stateCoverage symbolCoverage
    rowSlot cellSlot assignment accepted =
  placedPlainEndcapSound
    stateCoverage symbolCoverage
    (rowCellExtendedRename rowSlot cellSlot)
    assignment accepted

-- Construct a canonical RIGHTMOST column, not a user-selected proxy.
lastPhysicalColumn :
  (n : Nat) →
  Global.Slot n (suc n)
lastPhysicalColumn zero = Global.here
lastPhysicalColumn (suc n) = Global.there (lastPhysicalColumn n)

-- At any nonempty row width suc n, these are exactly the first/last
-- actual cells, each constrained on the SAME original global bits.
globalRowEndcapsCNF :
  ∀ {machine steps rowIndex}
    (colsMinusOne : Nat)
    (rowSlot : Global.Slot rowIndex (suc steps)) →
  CNF.CNF (Endpoint.ExtendedGlobalWidth machine steps (suc colsMinusOne))
globalRowEndcapsCNF colsMinusOne rowSlot =
  Placed.append
    (globalRowCellPlainCNF rowSlot Global.here)
    (globalRowCellPlainCNF rowSlot (lastPhysicalColumn colsMinusOne))

-- Enumerate every physical row slot 0 .. steps. The same list is used
-- for the concrete CNF and its proof-relevant evaluation certificate.
data SomeRowSlot (count : Nat) : Set where
  some-row-slot : ∀ {index} → Global.Slot index count → SomeRowSlot count

shiftRowSlots :
  ∀ {count} →
  List (SomeRowSlot count) → List (SomeRowSlot (suc count))
shiftRowSlots [] = []
shiftRowSlots (some-row-slot slot ∷ rest) =
  some-row-slot (Global.there slot) ∷ shiftRowSlots rest

allPhysicalRows : (count : Nat) → List (SomeRowSlot count)
allPhysicalRows zero = []
allPhysicalRows (suc count) =
  some-row-slot Global.here ∷ shiftRowSlots (allPhysicalRows count)

appendAllRowEndcaps :
  ∀ {machine steps}
    (colsMinusOne : Nat) →
  List (SomeRowSlot (suc steps)) →
  CNF.CNF (Endpoint.ExtendedGlobalWidth machine steps (suc colsMinusOne))
appendAllRowEndcaps colsMinusOne [] = []
appendAllRowEndcaps colsMinusOne (some-row-slot slot ∷ rest) =
  Placed.append
    (globalRowEndcapsCNF colsMinusOne slot)
    (appendAllRowEndcaps colsMinusOne rest)

-- Actual polynomially replicated row-boundary constraints over the
-- original extended vector. This is intentionally separate from the
-- pre-existing globalCookLevinCNF until the same-object decoded
-- endcap soundness and completeness consumers are welded.
globalAllRowsEndcapsCNF :
  ∀ {machine steps}
    (colsMinusOne : Nat) →
  CNF.CNF (Endpoint.ExtendedGlobalWidth machine steps (suc colsMinusOne))
globalAllRowsEndcapsCNF {steps = steps} colsMinusOne =
  appendAllRowEndcaps colsMinusOne (allPhysicalRows (suc steps))

-- The exact AND refinement for every emitted row. In particular this
-- certificate does not select just an arbitrary compatible row.
data AllPhysicalRowEndcapsTrue
    {machine steps}
    (colsMinusOne : Nat)
    (assignment :
      CNF.Bits (Endpoint.ExtendedGlobalWidth machine steps (suc colsMinusOne))) :
    List (SomeRowSlot (suc steps)) → Set where
  all-row-endcaps-done :
    AllPhysicalRowEndcapsTrue colsMinusOne assignment []
  all-row-endcaps-step :
    ∀ {index rest} (slot : Global.Slot index (suc steps)) →
    CNF.evaluateCNF
      (globalRowEndcapsCNF colsMinusOne slot) assignment ≡ true →
    AllPhysicalRowEndcapsTrue colsMinusOne assignment rest →
    AllPhysicalRowEndcapsTrue colsMinusOne assignment
      (some-row-slot slot ∷ rest)

andLeftTrue :
  ∀ left right →
  CNF.andBool left right ≡ true → left ≡ true
andLeftTrue false right ()
andLeftTrue true right proof = refl

andRightTrue :
  ∀ left right →
  CNF.andBool left right ≡ true → right ≡ true
andRightTrue false right ()
andRightTrue true right proof = proof

appendAllRowEndcapsSound :
  ∀ {machine steps}
    (colsMinusOne : Nat)
    (slots : List (SomeRowSlot (suc steps)))
    (assignment :
      CNF.Bits (Endpoint.ExtendedGlobalWidth machine steps (suc colsMinusOne))) →
  CNF.evaluateCNF
    (appendAllRowEndcaps colsMinusOne slots) assignment ≡ true →
  AllPhysicalRowEndcapsTrue colsMinusOne assignment slots
appendAllRowEndcapsSound colsMinusOne [] assignment accepted =
  all-row-endcaps-done
appendAllRowEndcapsSound colsMinusOne
    (some-row-slot slot ∷ rest) assignment accepted =
  all-row-endcaps-step slot
    (andLeftTrue left right split)
    (appendAllRowEndcapsSound colsMinusOne rest assignment
      (andRightTrue left right split))
  where
    left = CNF.evaluateCNF
      (globalRowEndcapsCNF colsMinusOne slot) assignment
    right = CNF.evaluateCNF
      (appendAllRowEndcaps colsMinusOne rest) assignment
    split : CNF.andBool left right ≡ true
    split with Placed.evaluateCNFAppend
      (globalRowEndcapsCNF colsMinusOne slot)
      (appendAllRowEndcaps colsMinusOne rest) assignment
    ... | refl = accepted

globalAllRowsEndcapsSound :
  ∀ {machine steps}
    (colsMinusOne : Nat)
    (assignment :
      CNF.Bits (Endpoint.ExtendedGlobalWidth machine steps (suc colsMinusOne))) →
  CNF.evaluateCNF (globalAllRowsEndcapsCNF colsMinusOne) assignment ≡ true →
  AllPhysicalRowEndcapsTrue colsMinusOne assignment
    (allPhysicalRows (suc steps))
globalAllRowsEndcapsSound {steps = steps}
    colsMinusOne assignment accepted =
  appendAllRowEndcapsSound colsMinusOne
    (allPhysicalRows (suc steps)) assignment accepted

------------------------------------------------------------------------
-- Genuine coverage: EVERY physical Global.Slot occurs in the exact
-- source-written allPhysicalRows enumeration. We can therefore select
-- the SAT-produced endcap certificate at any original row coordinate.
------------------------------------------------------------------------

data RowSlotMember {count : Nat} {index : Nat}
    (slot : Global.Slot index count) :
    List (SomeRowSlot count) → Set where
  row-member-here :
    ∀ {rest} →
    RowSlotMember slot (some-row-slot slot ∷ rest)
  row-member-there :
    ∀ {other rest} →
    RowSlotMember slot rest →
    RowSlotMember slot (other ∷ rest)

shiftRowSlotMember :
  ∀ {count index}
    {slot : Global.Slot index count}
    {rows : List (SomeRowSlot count)} →
  RowSlotMember slot rows →
  RowSlotMember (Global.there slot) (shiftRowSlots rows)
shiftRowSlotMember row-member-here = row-member-here
shiftRowSlotMember (row-member-there member) =
  row-member-there (shiftRowSlotMember member)

everyPhysicalRowIsEnumerated :
  ∀ {count index} (slot : Global.Slot index count) →
  RowSlotMember slot (allPhysicalRows count)
everyPhysicalRowIsEnumerated Global.here = row-member-here
everyPhysicalRowIsEnumerated (Global.there slot) =
  row-member-there
    (shiftRowSlotMember (everyPhysicalRowIsEnumerated slot))

selectRowEndcapCertificate :
  ∀ {machine steps rowIndex}
    (colsMinusOne : Nat)
    (assignment :
      CNF.Bits
        (Endpoint.ExtendedGlobalWidth machine steps (suc colsMinusOne)))
    (slot : Global.Slot rowIndex (suc steps))
    (rows : List (SomeRowSlot (suc steps))) →
  AllPhysicalRowEndcapsTrue colsMinusOne assignment rows →
  RowSlotMember slot rows →
  CNF.evaluateCNF
    (globalRowEndcapsCNF colsMinusOne slot) assignment ≡ true
selectRowEndcapCertificate colsMinusOne assignment slot
    (some-row-slot .slot ∷ rows)
    (all-row-endcaps-step .slot current rest)
    row-member-here =
  current
selectRowEndcapCertificate colsMinusOne assignment slot
    (some-row-slot other ∷ rows)
    (all-row-endcaps-step other current rest)
    (row-member-there member) =
  selectRowEndcapCertificate
    colsMinusOne assignment slot rows rest member

everyRowEndcapCNFTrue :
  ∀ {machine steps rowIndex}
    (colsMinusOne : Nat)
    (assignment :
      CNF.Bits
        (Endpoint.ExtendedGlobalWidth machine steps (suc colsMinusOne)))
    (slot : Global.Slot rowIndex (suc steps)) →
  CNF.evaluateCNF
    (globalAllRowsEndcapsCNF colsMinusOne) assignment ≡ true →
  CNF.evaluateCNF
    (globalRowEndcapsCNF colsMinusOne slot) assignment ≡ true
everyRowEndcapCNFTrue {steps = steps}
    colsMinusOne assignment slot allAccepted =
  selectRowEndcapCertificate
    colsMinusOne assignment slot
    (allPhysicalRows (suc steps))
    (globalAllRowsEndcapsSound colsMinusOne assignment allAccepted)
    (everyPhysicalRowIsEnumerated slot)

record PhysicalRowEndcapCellsPlain
    {machine : Local.ConcreteTapeMachine}
    {steps rowIndex colsMinusOne : Nat}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (rowSlot : Global.Slot rowIndex (suc steps))
    (assignment :
      CNF.Bits
        (Endpoint.ExtendedGlobalWidth machine steps (suc colsMinusOne))) :
    Set where
  field
    firstPhysicalCellIsPlain :
      Pattern.IsPlainCell
        (Canonical.decodeCell stateCoverage symbolCoverage
          (Rename.pullbackBits
            (rowCellExtendedRename rowSlot Global.here) assignment))
    lastPhysicalCellIsPlain :
      Pattern.IsPlainCell
        (Canonical.decodeCell stateCoverage symbolCoverage
          (Rename.pullbackBits
            (rowCellExtendedRename
              rowSlot (lastPhysicalColumn colsMinusOne)) assignment))

open PhysicalRowEndcapCellsPlain public

globalRowEndcapsSound :
  ∀ {machine steps rowIndex}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (colsMinusOne : Nat)
    (rowSlot : Global.Slot rowIndex (suc steps))
    (assignment :
      CNF.Bits
        (Endpoint.ExtendedGlobalWidth machine steps (suc colsMinusOne))) →
  CNF.evaluateCNF
    (globalRowEndcapsCNF colsMinusOne rowSlot) assignment ≡ true →
  PhysicalRowEndcapCellsPlain
    stateCoverage symbolCoverage rowSlot assignment
globalRowEndcapsSound stateCoverage symbolCoverage
    colsMinusOne rowSlot assignment accepted = record
  { firstPhysicalCellIsPlain =
      globalRowCellPlainSound stateCoverage symbolCoverage
        rowSlot Global.here assignment
        (andLeftTrue firstValue lastValue split)
  ; lastPhysicalCellIsPlain =
      globalRowCellPlainSound stateCoverage symbolCoverage
        rowSlot (lastPhysicalColumn colsMinusOne) assignment
        (andRightTrue firstValue lastValue split)
  }
  where
    firstCNF = globalRowCellPlainCNF rowSlot Global.here
    lastCNF = globalRowCellPlainCNF
      rowSlot (lastPhysicalColumn colsMinusOne)
    firstValue = CNF.evaluateCNF firstCNF assignment
    lastValue = CNF.evaluateCNF lastCNF assignment

    split : CNF.andBool firstValue lastValue ≡ true
    split with Placed.evaluateCNFAppend
      firstCNF lastCNF assignment
    ... | refl = accepted

globalAllRowsEndcapsGivePhysicalRowPlain :
  ∀ {machine steps rowIndex}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (colsMinusOne : Nat)
    (rowSlot : Global.Slot rowIndex (suc steps))
    (assignment :
      CNF.Bits
        (Endpoint.ExtendedGlobalWidth machine steps (suc colsMinusOne))) →
  CNF.evaluateCNF
    (globalAllRowsEndcapsCNF colsMinusOne) assignment ≡ true →
  PhysicalRowEndcapCellsPlain
    stateCoverage symbolCoverage rowSlot assignment
globalAllRowsEndcapsGivePhysicalRowPlain
    stateCoverage symbolCoverage colsMinusOne
    rowSlot assignment allAccepted =
  globalRowEndcapsSound
    stateCoverage symbolCoverage
    colsMinusOne rowSlot assignment
    (everyRowEndcapCNFTrue
      colsMinusOne assignment rowSlot allAccepted)

------------------------------------------------------------------------
-- Reverse direction: actual plain physical row endpoints imply the
-- SAT CNF, with one original row/column placement per fact.
-- This is the exact completeness constructor required for an
-- appropriately padded accepting-run assignment.
------------------------------------------------------------------------

globalRowEndcapsComplete :
  ∀ {machine steps rowIndex}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (colsMinusOne : Nat)
    (rowSlot : Global.Slot rowIndex (suc steps))
    (assignment :
      CNF.Bits
        (Endpoint.ExtendedGlobalWidth machine steps (suc colsMinusOne))) →
  PhysicalRowEndcapCellsPlain
    stateCoverage symbolCoverage rowSlot assignment →
  CNF.evaluateCNF
    (globalRowEndcapsCNF colsMinusOne rowSlot) assignment ≡ true
globalRowEndcapsComplete stateCoverage symbolCoverage
    colsMinusOne rowSlot assignment plain =
  trans
    (Placed.evaluateCNFAppend firstCNF lastCNF assignment)
    (cong₂ CNF.andBool firstAccepted lastAccepted)
  where
    firstCNF = globalRowCellPlainCNF rowSlot Global.here
    lastCNF =
      globalRowCellPlainCNF rowSlot
        (lastPhysicalColumn colsMinusOne)

    firstAccepted :
      CNF.evaluateCNF firstCNF assignment ≡ true
    firstAccepted =
      placedPlainEndcapComplete
        stateCoverage symbolCoverage
        (rowCellExtendedRename rowSlot Global.here)
        assignment
        (firstPhysicalCellIsPlain plain)

    lastAccepted :
      CNF.evaluateCNF lastCNF assignment ≡ true
    lastAccepted =
      placedPlainEndcapComplete
        stateCoverage symbolCoverage
        (rowCellExtendedRename
          rowSlot (lastPhysicalColumn colsMinusOne))
        assignment
        (lastPhysicalCellIsPlain plain)

allRowEndcapsComplete :
  ∀ {machine steps}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (colsMinusOne : Nat)
    (assignment :
      CNF.Bits
        (Endpoint.ExtendedGlobalWidth machine steps (suc colsMinusOne)))
    (rows : List (SomeRowSlot (suc steps))) →
  (∀ {rowIndex}
     (slot : Global.Slot rowIndex (suc steps)) →
    PhysicalRowEndcapCellsPlain
      stateCoverage symbolCoverage slot assignment) →
  CNF.evaluateCNF
    (appendAllRowEndcaps colsMinusOne rows) assignment ≡ true
allRowEndcapsComplete stateCoverage symbolCoverage
    colsMinusOne assignment [] allPlain = refl
allRowEndcapsComplete stateCoverage symbolCoverage
    colsMinusOne assignment (some-row-slot slot ∷ rest) allPlain =
  trans
    (Placed.evaluateCNFAppend
      (globalRowEndcapsCNF colsMinusOne slot)
      (appendAllRowEndcaps colsMinusOne rest)
      assignment)
    (cong₂ CNF.andBool
      (globalRowEndcapsComplete stateCoverage symbolCoverage
        colsMinusOne slot assignment (allPlain slot))
      (allRowEndcapsComplete stateCoverage symbolCoverage
        colsMinusOne assignment rest allPlain))

globalAllRowsEndcapsComplete :
  ∀ {machine steps}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (colsMinusOne : Nat)
    (assignment :
      CNF.Bits
        (Endpoint.ExtendedGlobalWidth machine steps (suc colsMinusOne))) →
  (∀ {rowIndex}
     (slot : Global.Slot rowIndex (suc steps)) →
    PhysicalRowEndcapCellsPlain
      stateCoverage symbolCoverage slot assignment) →
  CNF.evaluateCNF
    (globalAllRowsEndcapsCNF colsMinusOne) assignment ≡ true
globalAllRowsEndcapsComplete {steps = steps}
    stateCoverage symbolCoverage colsMinusOne assignment allPlain =
  allRowEndcapsComplete
    stateCoverage symbolCoverage colsMinusOne assignment
    (allPhysicalRows (suc steps)) allPlain
