module DASHI.Mathematics.Complexity.ConcreteTapePlacedWholeRowCNFExact where

------------------------------------------------------------------------
-- WHOLE ROW-PAIR SCAN -> ONE CONJUNCTION OF PLACED WINDOW CNFs
--
-- We rebuild the recursive 2x3 scanner with explicit IndexedSixCellWindow
-- witnesses.  Forgetting indices reproduces the existing semantic scanner.
-- Every emitted occurrence is therefore compiled by the canonical placement
-- theorem into the common flat row-pair variable space.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; _⊔_)
open import Agda.Builtin.Bool using (Bool; false; true)
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
  { leftAt = shiftAt (Indexed.leftAt triple)
  ; centerAt = shiftAt (Indexed.centerAt triple)
  ; rightAt = shiftAt (Indexed.rightAt triple)
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
  { index = suc (Indexed.index occurrence)
  ; oldLeft = Indexed.oldLeft occurrence
  ; oldCenter = Indexed.oldCenter occurrence
  ; oldRight = Indexed.oldRight occurrence
  ; newLeft = Indexed.newLeft occurrence
  ; newCenter = Indexed.newCenter occurrence
  ; newRight = Indexed.newRight occurrence
  ; oldTriple = shiftTriple (Indexed.oldTriple occurrence)
  ; newTriple = shiftTriple (Indexed.newTriple occurrence)
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
  { index = zero
  ; oldLeft = oldLeft
  ; oldCenter = oldCenter
  ; oldRight = oldRight
  ; newLeft = newLeft
  ; newCenter = newCenter
  ; newRight = newRight
  ; oldTriple = record
      { leftAt = Indexed.here
      ; centerAt = Indexed.there Indexed.here
      ; rightAt = Indexed.there (Indexed.there Indexed.here)
      }
  ; newTriple = record
      { leftAt = Indexed.here
      ; centerAt = Indexed.there Indexed.here
      ; rightAt = Indexed.there (Indexed.there Indexed.here)
      }
  }

------------------------------------------------------------------------
-- Indexed recursive scan
------------------------------------------------------------------------

mapShiftIndexedWindows :
  ∀ {machine}
    {beforeTail afterTail :
      List (Local.TapeCell
        (Local.State machine)
        (Local.Symbol machine))}
    (beforeHead afterHead :
      Local.TapeCell
        (Local.State machine)
        (Local.Symbol machine)) →
  List
    (Indexed.IndexedSixCellWindow
      machine
      (Local.tape-row beforeTail)
      (Local.tape-row afterTail)) →
  List
    (Indexed.IndexedSixCellWindow
      machine
      (Local.tape-row (beforeHead ∷ beforeTail))
      (Local.tape-row (afterHead ∷ afterTail)))
mapShiftIndexedWindows beforeHead afterHead [] = []
mapShiftIndexedWindows beforeHead afterHead (occurrence ∷ rest) =
  shiftIndexedWindow beforeHead afterHead occurrence
  ∷ mapShiftIndexedWindows beforeHead afterHead rest

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
  ∷ mapShiftIndexedWindows oldLeft newLeft
      (scanIndexedWindowsCells machine
        (oldCenter ∷ oldRight ∷ oldRest)
        (newCenter ∷ newRight ∷ newRest))
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

mapForget_mapShift :
  ∀ {machine}
    {beforeTail afterTail :
      List (Local.TapeCell
        (Local.State machine)
        (Local.Symbol machine))}
    (beforeHead afterHead :
      Local.TapeCell
        (Local.State machine)
        (Local.Symbol machine))
    (xs :
      List
        (Indexed.IndexedSixCellWindow
          machine
          (Local.tape-row beforeTail)
          (Local.tape-row afterTail))) →
  mapForgetIndexed (mapShiftIndexedWindows beforeHead afterHead xs)
  ≡ mapForgetIndexed xs
mapForget_mapShift beforeHead afterHead [] = refl
mapForget_mapShift beforeHead afterHead (occurrence ∷ rest) =
  cong (Indexed.forgetIndex occurrence ∷_)
    (mapForget_mapShift beforeHead afterHead rest)

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
    (Local.tape-row (newLeft ∷ newCenter ∷ newRight ∷ newRest)) =
  cong (Local.six-cell-window oldLeft oldCenter oldRight newLeft newCenter newRight ∷_)
    (trans
      (mapForget_mapShift oldLeft newLeft
        (scanIndexedWindowsCells machine
          (oldCenter ∷ oldRight ∷ oldRest)
          (newCenter ∷ newRight ∷ newRest)))
      (scanIndexed_forget machine
        (Local.tape-row (oldCenter ∷ oldRight ∷ oldRest))
        (Local.tape-row (newCenter ∷ newRight ∷ newRest))))

------------------------------------------------------------------------
-- Compile every indexed window into the common global row-pair variable space
------------------------------------------------------------------------

compileIndexedWindows :
  ∀ {machine before after}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (rule : Local.TapeRule
      (Local.State machine)
      (Local.Symbol machine)) →
  List (Indexed.IndexedSixCellWindow machine before after) →
  List
    (Placed.PlacedPredicate
      (Canonical.WindowWidth machine)
      (Flat.RowPairWidth before after))
compileIndexedWindows stateCoverage symbolCoverage rule [] = []
compileIndexedWindows stateCoverage symbolCoverage rule (occurrence ∷ rest) =
  PlacedWindow.indexedWindowPlacedPredicate
    stateCoverage symbolCoverage rule occurrence
  ∷ compileIndexedWindows stateCoverage symbolCoverage rule rest

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
  compileIndexedWindows stateCoverage symbolCoverage rule
    (scanIndexedWindows _ before after)

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
    List (Indexed.IndexedSixCellWindow machine before after) → Set₁ where
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
  Placed.AllPlacedSatisfied
    (Flat.encodeRowPair stateCoverage symbolCoverage before after)
    (compileIndexedWindows stateCoverage symbolCoverage rule occurrences)
allIndexedLegalImpliesPlacedPredicates {machine} {before} {after} {rule}
    stateCoverage symbolCoverage
    [] allIndexedNil =
  Placed.allPlacedDone
allIndexedLegalImpliesPlacedPredicates {machine} {before} {after} {rule}
    stateCoverage symbolCoverage
    (occurrence ∷ rest)
    (allIndexedCons legal restLegal) =
  Placed.allPlacedStep
    (PlacedWindow.semanticLegalIndexedWindowImpliesPlacedPredicate
      stateCoverage symbolCoverage rule occurrence legal)
    (allIndexedLegalImpliesPlacedPredicates {machine} {before} {after} {rule}
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
allIndexedLegalImpliesWholeRowPlacedCNF {machine} {before} {after} {rule}
    stateCoverage symbolCoverage legal =
  Placed.compilePlacedAllComplete
    (placedPredicatesForIndexedScan
      stateCoverage symbolCoverage rule before after)
    (Flat.encodeRowPair stateCoverage symbolCoverage before after)
    (allIndexedLegalImpliesPlacedPredicates {machine} {before} {after} {rule}
      stateCoverage symbolCoverage
      (scanIndexedWindows machine before after) legal)


placedPredicatesImpliesAllIndexedLegal :
  ∀ {machine before after rule}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (occurrences :
      List (Indexed.IndexedSixCellWindow machine before after)) →
  Placed.AllPlacedSatisfied
    (Flat.encodeRowPair stateCoverage symbolCoverage before after)
    (compileIndexedWindows stateCoverage symbolCoverage rule occurrences) →
  AllIndexedLegal rule occurrences
placedPredicatesImpliesAllIndexedLegal
    stateCoverage symbolCoverage
    [] Placed.allPlacedDone =
  allIndexedNil
placedPredicatesImpliesAllIndexedLegal {machine} {before} {after} {rule}
    stateCoverage symbolCoverage
    (occurrence ∷ rest)
    (Placed.allPlacedStep accepted restAccepted) =
  allIndexedCons
    (PlacedWindow.placedPredicateImpliesSemanticLegalIndexedWindow
      stateCoverage symbolCoverage rule occurrence accepted)
    (placedPredicatesImpliesAllIndexedLegal {machine} {before} {after} {rule}
      stateCoverage symbolCoverage rest restAccepted)

wholeRowPlacedCNFImpliesAllIndexedLegal :
  ∀ {machine before after rule}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine)) →
  CNF.evaluateCNF
    (wholeRowPlacedCNF
      stateCoverage symbolCoverage rule before after)
    (Flat.encodeRowPair stateCoverage symbolCoverage before after)
  ≡ true →
  AllIndexedLegal rule
    (scanIndexedWindows machine before after)
wholeRowPlacedCNFImpliesAllIndexedLegal {machine} {before} {after} {rule}
    stateCoverage symbolCoverage accepted =
  placedPredicatesImpliesAllIndexedLegal {machine} {before} {after} {rule}
    stateCoverage symbolCoverage
    (scanIndexedWindows machine before after)
    (Placed.compilePlacedAllSound
      (placedPredicatesForIndexedScan
        stateCoverage symbolCoverage rule before after)
      (Flat.encodeRowPair stateCoverage symbolCoverage before after)
      accepted)

record _↔_ {ℓ₁ ℓ₂ : Level} (A : Set ℓ₁) (B : Set ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
  field
    to : A → B
    from : B → A

wholeRowPlacedCNF_iff_allIndexedLegal :
  ∀ {machine before after rule}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine)) →
  (CNF.evaluateCNF
    (wholeRowPlacedCNF
      stateCoverage symbolCoverage rule before after)
    (Flat.encodeRowPair stateCoverage symbolCoverage before after)
    ≡ true)
  ↔
  AllIndexedLegal rule
    (scanIndexedWindows machine before after)
wholeRowPlacedCNF_iff_allIndexedLegal
    stateCoverage symbolCoverage =
  record
    { to =
        wholeRowPlacedCNFImpliesAllIndexedLegal
          stateCoverage symbolCoverage
    ; from =
        allIndexedLegalImpliesWholeRowPlacedCNF
          stateCoverage symbolCoverage
    }

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
  ; wholeRowCNFImpliesLegalScanPaid = true
  ; endpointClausePlacementPaid = false
  ; runLevelGlobalOffsetPlacementPaid = false
  ; acceptingRunIffSATPaid = false
  ; polynomialManyOneReductionPaid = false
  ; pVsNPResolved = false
  }
