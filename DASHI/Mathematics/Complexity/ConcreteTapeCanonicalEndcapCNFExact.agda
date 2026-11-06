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
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
import Data.Fin.Base as Fin

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeCanonicalCellBitsExact as Canonical
import DASHI.Mathematics.Complexity.ConcreteTapeLocalWindowPatternsExact as Pattern
import DASHI.Mathematics.Complexity.FixedWidthTruthTableCNFExact as CNF
import DASHI.Mathematics.Complexity.CNFVariableRenamingExact as Rename
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
  appendCNFs
    (globalRowCellPlainCNF rowSlot Global.here)
    (globalRowCellPlainCNF rowSlot (lastPhysicalColumn colsMinusOne))
  where
    appendCNFs :
      ∀ {n} → CNF.CNF n → CNF.CNF n → CNF.CNF n
    appendCNFs [] right = right
    appendCNFs (first ∷ rest) right =
      first ∷ appendCNFs rest right
