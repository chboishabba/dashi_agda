module DASHI.Mathematics.Complexity.ConcreteTapePlacedWholeRowCNFExact where

------------------------------------------------------------------------
-- WHOLE ROW-PAIR SCAN -> ONE CONJUNCTION OF PLACED WINDOW CNFs
--
-- We rebuild the recursive 2x3 scanner with explicit IndexedSixCellWindow
-- witnesses.  Forgetting indices reproduces the existing semantic scanner.
-- Every emitted occurrence is therefore compiled by the canonical placement
-- theorem into the common flat row-pair variable space.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeIndexedWindowExact as Indexed
import DASHI.Mathematics.Complexity.ConcreteTapeWholeRowLocalityExact as Whole
import DASHI.Mathematics.Complexity.ConcreteTapeCanonicalCellBitsExact as Canonical
import DASHI.Mathematics.Complexity.ConcreteTapeFlatAssignmentExact as Flat
import DASHI.Mathematics.Complexity.ConcreteTapePlacedWindowCNFExact as PlacedWindow
import DASHI.Mathematics.Complexity.CNFPlacedConstraintConjunctionExact as Placed
import DASHI.Mathematics.Complexity.FixedWidthTruthTableCNFExact as CNF
import DASHI.Mathematics.Complexity.ConcreteTapeLocalWindowPatternsExact as Pattern

------------------------------------------------------------------------
-- Index-shifting geometry
------------------------------------------------------------------------

shiftAt :
  ∀ {A : Set} {n : Nat} {x head : A} {xs : List A} →
  Indexed.At n x xs →
  Indexed.At (suc n) x (head ∷ xs)
shiftAt = Indexed.there

shiftTriple :
  ∀ {A : Set} {n : Nat}
    {left center right head : A} {xs : List A} →
  Indexed.TripleAt n left center right xs →
  Indexed.TripleAt
    (suc n) left center right (head ∷ xs)
shiftTriple triple = record
  { Indexed.leftAt = shiftAt (Indexed.leftAt triple)
  ; Indexed.centerAt = shiftAt (Indexed.centerAt triple)
  ; Indexed.rightAt = shiftAt (Indexed.rightAt triple)
  }

shiftIndexedWindow :
  ∀ {machine}
    {beforeTail afterTail :
      List (Local.TapeCell
        (Local.State machine)
        (Local.Symbol machine))}
    (beforeHead afterHead :
      Local.TapeCell
        (Local.State machine)
        (Local.Symbol machine)) →
  Indexed.IndexedSixCellWindow
    machine
    (Local.tape-row beforeTail)
    (Local.tape-row afterTail) →
  Indexed.IndexedSixCellWindow
    machine
    (Local.tape-row (beforeHead ∷ beforeTail))
    (Local.tape-row (afterHead ∷ afterTail))
shiftIndexedWindow beforeHead afterHead occurrence = record
  { Indexed.index = suc (Indexed.index occurrence)
  ; Indexed.oldLeft = Indexed.oldLeft occurrence
  ; Indexed.oldCenter = Indexed.oldCenter occurrence
  ; Indexed.oldRight = Indexed.oldRight occurrence
  ; Indexed.newLeft = Indexed.newLeft occurrence
  ; Indexed.newCenter = Indexed.newCenter occurrence
  ; Indexed.newRight = Indexed.newRight occurrence
  ; Indexed.oldTriple = shiftTriple (Indexed.oldTriple occurrence)
  ; Indexed.newTriple = shiftTriple (Indexed.newTriple occurrence)
  }

headIndexedWindow :
  ∀ {machine}
    (oldLeft oldCenter oldRight :
      Local.TapeCell
        (Local.State machine)
        (Local.Symbol machine))
    (oldRest :
      List (Local.TapeCell
        (Local.State machine)
        (Local.Symbol machine)))
    (newLeft newCenter newRight :
      Local.TapeCell
        (Local.State machine)
        (Local.Symbol machine))
    (newRest :
      List (Local.TapeCell
        (Local.State machine)
        (Local.Symbol machine))) →
  Indexed.IndexedSixCellWindow
    machine
    (Local.tape-row (oldLeft ∷ oldCenter ∷ oldRight ∷ oldRest))
    (Local.tape-row (newLeft ∷ newCenter ∷ newRight ∷ newRest))
headIndexedWindow
    oldLeft oldCenter oldRight oldRest
    newLeft newCenter newRight newRest = record
  { Indexed.index = zero
  ; Indexed.oldLeft = oldLeft
  ; Indexed.oldCenter = oldCenter
  ; Indexed.oldRight = oldRight
  ; Indexed.newLeft = newLeft
  ; Indexed.newCenter = newCenter
  ; Indexed.newRight = newRight
  ; Indexed.oldTriple = record
      { Indexed.leftAt = Indexed.here
      ; Indexed.centerAt = Indexed.there Indexed.here
      ; Indexed.rightAt = Indexed.there (Indexed.there Indexed.here)
      }
  ; Indexed.newTriple = record
      { Indexed.leftAt = Indexed.here
      ; Indexed.centerAt = Indexed.there Indexed.here
      ; Indexed.rightAt = Indexed.there (Indexed.there Indexed.here)
      }
  }

------------------------------------------------------------------------
-- Indexed recursive scan
------------------------------------------------------------------------

scanIndexedWindowsCells :
  (machine : Local.ConcreteTapeMachine) →
  (beforeCells afterCells :
    List (Local.TapeCell
      (Local.State machine)
      (Local.Symbol machine))) →
  List
    (Indexed.IndexedSixCellWindow
      machine
      (Local.tape-row beforeCells)
      (Local.tape-row afterCells))
scanIndexedWindowsCells machine
    (oldLeft ∷ oldCenter ∷ oldRight ∷ oldRest)
    (newLeft ∷ newCenter ∷ newRight ∷ newRest) =
  headIndexedWindow
      oldLeft oldCenter oldRight oldRest
      newLeft newCenter newRight newRest
  ∷ mapShift
      (scanIndexedWindowsCells machine
        (oldCenter ∷ oldRight ∷ oldRest)
        (newCenter ∷ newRight ∷ newRest))
  where
    mapShift :
      List
        (Indexed.IndexedSixCellWindow
          machine
          (Local.tape-row (oldCenter ∷ oldRight ∷ oldRest))
          (Local.tape-row (newCenter ∷ newRight ∷ newRest))) →
      List
        (Indexed.IndexedSixCellWindow
          machine
          (Local.tape-row (oldLeft ∷ oldCenter ∷ oldRight ∷ oldRest))
          (Local.tape-row (newLeft ∷ newCenter ∷ newRight ∷ newRest)))
    mapShift [] = []
    mapShift (occurrence ∷ rest) =
      shiftIndexedWindow oldLeft newLeft occurrence
      ∷ mapShift rest
scanIndexedWindowsCells machine _ _ = []

scanIndexedWindows :
  (machine : Local.ConcreteTapeMachine) →
  (before after : Local.TapeRow machine) →
  List (Indexed.IndexedSixCellWindow machine before after)
scanIndexedWindows machine
    (Local.tape-row beforeCells)
    (Local.tape-row afterCells) =
  scanIndexedWindowsCells machine beforeCells afterCells

------------------------------------------------------------------------
-- Forgetting coordinates recovers the old scanner
------------------------------------------------------------------------

mapForgetIndexed :
  ∀ {machine before after} →
  List (Indexed.IndexedSixCellWindow machine before after) →
  List (Local.SixCellWindow machine)
mapForgetIndexed [] = []
mapForgetIndexed (occurrence ∷ rest) =
  Indexed.forgetIndex occurrence ∷ mapForgetIndexed rest

scanIndexed_forget :
  ∀ (machine : Local.ConcreteTapeMachine)
    (before after : Local.TapeRow machine) →
  mapForgetIndexed (scanIndexedWindows machine before after)
  ≡ Whole.scanWindows machine before after
scanIndexed_forget machine
    (Local.tape-row [])
    (Local.tape-row afterCells) =
  refl
scanIndexed_forget machine
    (Local.tape-row (x ∷ []))
    (Local.tape-row afterCells) =
  refl
scanIndexed_forget machine
    (Local.tape-row (x ∷ y ∷ []))
    (Local.tape-row afterCells) =
  refl
scanIndexed_forget machine
    (Local.tape-row (oldLeft ∷ oldCenter ∷ oldRight ∷ oldRest))
    (Local.tape-row []) =
  refl
scanIndexed_forget machine
    (Local.tape-row (oldLeft ∷ oldCenter ∷ oldRight ∷ oldRest))
    (Local.tape-row (x ∷ [])) =
  refl
scanIndexed_forget machine
    (Local.tape-row (oldLeft ∷ oldCenter ∷ oldRight ∷ oldRest))
    (Local.tape-row (x ∷ y ∷ [])) =
  refl
scanIndexed_forget machine
    (Local.tape-row (oldLeft ∷ oldCenter ∷ oldRight ∷ oldRest))
    (Local.tape-row (newLeft ∷ newCenter ∷ newRight ∷ newRest))
    rewrite scanIndexed_forget machine
      (Local.tape-row (oldCenter ∷ oldRight ∷ oldRest))
      (Local.tape-row (newCenter ∷ newRight ∷ newRest)) =
  refl

------------------------------------------------------------------------
-- Compile every indexed window into the common global row-pair variable space
------------------------------------------------------------------------

placedPredicatesForIndexedScan :
  ∀ {machine}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (rule : Local.TapeRule
      (Local.State machine)
      (Local.Symbol machine))
    (before after : Local.TapeRow machine) →
  List
    (Placed.PlacedPredicate
      (Canonical.WindowWidth machine)
      (Flat.RowPairWidth before after))
placedPredicatesForIndexedScan
    stateCoverage symbolCoverage rule before after =
  go (scanIndexedWindows _ before after)
  where
    go :
      List (Indexed.IndexedSixCellWindow _ before after) →
      List
        (Placed.PlacedPredicate
          (Canonical.WindowWidth _)
          (Flat.RowPairWidth before after))
    go [] = []
    go (occurrence ∷ rest) =
      PlacedWindow.indexedWindowPlacedPredicate
        stateCoverage symbolCoverage rule occurrence
      ∷ go rest

wholeRowPlacedCNF :
  ∀ {machine}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (rule : Local.TapeRule
      (Local.State machine)
      (Local.Symbol machine))
    (before after : Local.TapeRow machine) →
  CNF.CNF (Flat.RowPairWidth before after)
wholeRowPlacedCNF
    stateCoverage symbolCoverage rule before after =
  Placed.compilePlacedAll
    (placedPredicatesForIndexedScan
      stateCoverage symbolCoverage rule before after)

data AllIndexedLegal
    {machine}
    (rule : Local.TapeRule
      (Local.State machine)
      (Local.Symbol machine))
    {before after : Local.TapeRow machine} :
    List (Indexed.IndexedSixCellWindow machine before after) → Set where
  allIndexedNil :
    AllIndexedLegal rule []
  allIndexedCons :
    ∀ {occurrence rest} →
    Pattern.LegalWindowForRule
      machine rule (Indexed.forgetIndex occurrence) →
    AllIndexedLegal rule rest →
    AllIndexedLegal rule (occurrence ∷ rest)

allIndexedLegalImpliesPlacedPredicates :
  ∀ {machine before after rule}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (occurrences :
      List (Indexed.IndexedSixCellWindow machine before after)) →
  AllIndexedLegal rule occurrences →
  Placed.AllPlacedPredicatesHold
    (compile occurrences)
    (Flat.encodeRowPair stateCoverage symbolCoverage before after)
  where
    compile :
      List (Indexed.IndexedSixCellWindow machine before after) →
      List
        (Placed.PlacedPredicate
          (Canonical.WindowWidth machine)
          (Flat.RowPairWidth before after))
    compile [] = []
    compile (occurrence ∷ rest) =
      PlacedWindow.indexedWindowPlacedPredicate
        stateCoverage symbolCoverage rule occurrence
      ∷ compile rest
allIndexedLegalImpliesPlacedPredicates
    stateCoverage symbolCoverage
    [] allIndexedNil =
  Placed.allPlacedDone
allIndexedLegalImpliesPlacedPredicates
    stateCoverage symbolCoverage
    (occurrence ∷ rest)
    (allIndexedCons legal restLegal) =
  Placed.allPlacedStep
    (PlacedWindow.semanticLegalIndexedWindowImpliesPlacedPredicate
      stateCoverage symbolCoverage _ occurrence legal)
    (allIndexedLegalImpliesPlacedPredicates
      stateCoverage symbolCoverage rest restLegal)

allIndexedLegalImpliesWholeRowPlacedCNF :
  ∀ {machine before after rule}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine)) →
  AllIndexedLegal rule
    (scanIndexedWindows machine before after) →
  CNF.evaluateCNF
    (wholeRowPlacedCNF
      stateCoverage symbolCoverage rule before after)
    (Flat.encodeRowPair stateCoverage symbolCoverage before after)
  ≡ true
allIndexedLegalImpliesWholeRowPlacedCNF
    stateCoverage symbolCoverage legal =
  Placed.compilePlacedAllComplete
    (placedPredicatesForIndexedScan
      stateCoverage symbolCoverage _ _ _)
    (Flat.encodeRowPair stateCoverage symbolCoverage _ _)
    (allIndexedLegalImpliesPlacedPredicates
      stateCoverage symbolCoverage
      (scanIndexedWindows _ _ _) legal)

record PlacedWholeRowCNFReceipt
    (machine : Local.ConcreteTapeMachine) : Set₁ where
  field
    stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine)
    symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine)

    indexedWholeRowScanPaid : Bool
    forgetIndexedEqualsSemanticScanPaid : Bool
    perWindowPlacementPaid : Bool
    wholeRowPlacedConjunctionPaid : Bool
    legalScanImpliesWholeRowCNFPaid : Bool
    wholeRowCNFImpliesLegalScanPaid : Bool
    endpointClausePlacementPaid : Bool
    runLevelGlobalOffsetPlacementPaid : Bool
    acceptingRunIffSATPaid : Bool
    polynomialManyOneReductionPaid : Bool
    pVsNPResolved : Bool

canonicalPlacedWholeRowCNFReceipt :
  ∀ (machine : Local.ConcreteTapeMachine)
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine)) →
  PlacedWholeRowCNFReceipt machine
canonicalPlacedWholeRowCNFReceipt machine stateCoverage symbolCoverage = record
  { stateCoverage = stateCoverage
  ; symbolCoverage = symbolCoverage
  ; indexedWholeRowScanPaid = true
  ; forgetIndexedEqualsSemanticScanPaid = true
  ; perWindowPlacementPaid = true
  ; wholeRowPlacedConjunctionPaid = true
  ; legalScanImpliesWholeRowCNFPaid = true
  ; wholeRowCNFImpliesLegalScanPaid = false
  ; endpointClausePlacementPaid = false
  ; runLevelGlobalOffsetPlacementPaid = false
  ; acceptingRunIffSATPaid = false
  ; polynomialManyOneReductionPaid = false
  ; pVsNPResolved = false
  }
