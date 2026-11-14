module DASHI.Mathematics.Complexity.ConcreteTapePlacedWindowCNFExact where

------------------------------------------------------------------------
-- ACTUAL INDEXED WINDOW -> PLACED LOCAL CNF ON THE FLAT ROW-PAIR ASSIGNMENT
--
-- The preceding placement theorem proves that pulling the global row-pair
-- assignment back along indexedWindowRename gives exactly the canonical
-- six-cell code.  Therefore the generic PlacedPredicate / truth-table CNF
-- compiler can now be instantiated on the actual concrete tape representation.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; trans; subst; sym)

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeIndexedWindowExact as Indexed
import DASHI.Mathematics.Complexity.ConcreteTapeCanonicalCellBitsExact as Canonical
import DASHI.Mathematics.Complexity.ConcreteTapeFlatAssignmentExact as Flat
import DASHI.Mathematics.Complexity.ConcreteTapeCanonicalWindowPlacementExact as Placement
import DASHI.Mathematics.Complexity.ConcreteTapeWindowCodecCNFWeldExact as Window
import DASHI.Mathematics.Complexity.ConcreteTapeLegalWindowReflectionExact as Reflect
import DASHI.Mathematics.Complexity.ConcreteTapeLocalWindowPatternsExact as Pattern
import DASHI.Mathematics.Complexity.CNFPlacedConstraintConjunctionExact as Placed
import DASHI.Mathematics.Complexity.CNFVariableRenamingExact as Rename
import DASHI.Mathematics.Complexity.FixedWidthTruthTableCNFExact as CNF

indexedWindowPlacedPredicate :
  ∀ {machine before after}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (rule : Local.TapeRule
      (Local.State machine)
      (Local.Symbol machine))
    (occurrence : Indexed.IndexedSixCellWindow machine before after) →
  Placed.PlacedPredicate
    (Canonical.WindowWidth machine)
    (Flat.RowPairWidth before after)
indexedWindowPlacedPredicate {machine}
    stateCoverage symbolCoverage rule occurrence =
  Placed.placed-predicate
    (Placement.indexedWindowRename
      stateCoverage symbolCoverage occurrence)
    (Window.encodedWindowPredicate
      (Canonical.canonicalWindowCodec
        machine stateCoverage symbolCoverage)
      rule)

indexedWindowPulledPredicate_is_reflectedWindow :
  ∀ {machine before after}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (rule : Local.TapeRule
      (Local.State machine)
      (Local.Symbol machine))
    (occurrence : Indexed.IndexedSixCellWindow machine before after) →
  Placed.predicate
    (indexedWindowPlacedPredicate
      stateCoverage symbolCoverage rule occurrence)
    (Rename.pullbackBits
      (Placed.rename
        (indexedWindowPlacedPredicate
          stateCoverage symbolCoverage rule occurrence))
      (Flat.encodeRowPair
        stateCoverage symbolCoverage before after))
  ≡ Reflect.reflectedLegalWindowBool
      machine rule (Indexed.forgetIndex occurrence)
indexedWindowPulledPredicate_is_reflectedWindow
    {machine} {before} {after}
    stateCoverage symbolCoverage rule occurrence =
  trans
    (cong (Window.encodedWindowPredicate codec rule)
      (Placement.indexedWindowPullback_is_canonicalWindowEncoding
        stateCoverage symbolCoverage occurrence))
    (cong (Reflect.reflectedLegalWindowBool machine rule)
      (Window.FixedWidthWindowCodec.decodeEncode codec
        (Indexed.forgetIndex occurrence)))
  where
    codec =
      Canonical.canonicalWindowCodec
        machine stateCoverage symbolCoverage

semanticLegalIndexedWindowImpliesPlacedPredicate :
  ∀ {machine before after}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (rule : Local.TapeRule
      (Local.State machine)
      (Local.Symbol machine))
    (occurrence : Indexed.IndexedSixCellWindow machine before after) →
  Pattern.LegalWindowForRule
    machine rule (Indexed.forgetIndex occurrence) →
  Placed.predicate
    (indexedWindowPlacedPredicate
      stateCoverage symbolCoverage rule occurrence)
    (Rename.pullbackBits
      (Placed.rename
        (indexedWindowPlacedPredicate
          stateCoverage symbolCoverage rule occurrence))
      (Flat.encodeRowPair
        stateCoverage symbolCoverage before after))
  ≡ true
semanticLegalIndexedWindowImpliesPlacedPredicate
    stateCoverage symbolCoverage rule occurrence legal =
  trans
    (indexedWindowPulledPredicate_is_reflectedWindow
      stateCoverage symbolCoverage rule occurrence)
    (Reflect.semanticLegalImpliesReflectedBooleanTrue legal)

placedPredicateImpliesSemanticLegalIndexedWindow :
  ∀ {machine before after}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (rule : Local.TapeRule
      (Local.State machine)
      (Local.Symbol machine))
    (occurrence : Indexed.IndexedSixCellWindow machine before after) →
  Placed.predicate
    (indexedWindowPlacedPredicate
      stateCoverage symbolCoverage rule occurrence)
    (Rename.pullbackBits
      (Placed.rename
        (indexedWindowPlacedPredicate
          stateCoverage symbolCoverage rule occurrence))
      (Flat.encodeRowPair
        stateCoverage symbolCoverage before after))
  ≡ true →
  Pattern.LegalWindowForRule
    machine rule (Indexed.forgetIndex occurrence)
placedPredicateImpliesSemanticLegalIndexedWindow
    stateCoverage symbolCoverage rule occurrence accepted =
  Reflect.booleanTrueImpliesSemanticLegal
    (trans
      (sym
        (indexedWindowPulledPredicate_is_reflectedWindow
          stateCoverage symbolCoverage rule occurrence))
      accepted)

indexedWindowPlacedCNF :
  ∀ {machine before after}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (rule : Local.TapeRule
      (Local.State machine)
      (Local.Symbol machine))
    (occurrence : Indexed.IndexedSixCellWindow machine before after) →
  CNF.CNF (Flat.RowPairWidth before after)
indexedWindowPlacedCNF stateCoverage symbolCoverage rule occurrence =
  Placed.compilePlaced
    (indexedWindowPlacedPredicate
      stateCoverage symbolCoverage rule occurrence)

semanticLegalIndexedWindowImpliesPlacedCNF :
  ∀ {machine before after}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (rule : Local.TapeRule
      (Local.State machine)
      (Local.Symbol machine))
    (occurrence : Indexed.IndexedSixCellWindow machine before after) →
  Pattern.LegalWindowForRule
    machine rule (Indexed.forgetIndex occurrence) →
  CNF.evaluateCNF
    (indexedWindowPlacedCNF
      stateCoverage symbolCoverage rule occurrence)
    (Flat.encodeRowPair stateCoverage symbolCoverage before after)
  ≡ true
semanticLegalIndexedWindowImpliesPlacedCNF {before = before} {after = after}
    stateCoverage symbolCoverage rule occurrence legal =
  Rename.placedTruthTableCNFComplete
    (Placed.rename
      (indexedWindowPlacedPredicate stateCoverage symbolCoverage rule occurrence))
    (Placed.predicate
      (indexedWindowPlacedPredicate stateCoverage symbolCoverage rule occurrence))
    (Flat.encodeRowPair stateCoverage symbolCoverage before after)
    (semanticLegalIndexedWindowImpliesPlacedPredicate
      stateCoverage symbolCoverage rule occurrence legal)

placedCNFImpliesSemanticLegalIndexedWindow :
  ∀ {machine before after}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (rule : Local.TapeRule
      (Local.State machine)
      (Local.Symbol machine))
    (occurrence : Indexed.IndexedSixCellWindow machine before after) →
  CNF.evaluateCNF
    (indexedWindowPlacedCNF
      stateCoverage symbolCoverage rule occurrence)
    (Flat.encodeRowPair stateCoverage symbolCoverage before after)
  ≡ true →
  Pattern.LegalWindowForRule
    machine rule (Indexed.forgetIndex occurrence)
placedCNFImpliesSemanticLegalIndexedWindow {before = before} {after = after}
    stateCoverage symbolCoverage rule occurrence accepted =
  placedPredicateImpliesSemanticLegalIndexedWindow
    stateCoverage symbolCoverage rule occurrence
    (Rename.placedTruthTableCNFSound
      (Placed.rename
        (indexedWindowPlacedPredicate stateCoverage symbolCoverage rule occurrence))
      (Placed.predicate
        (indexedWindowPlacedPredicate stateCoverage symbolCoverage rule occurrence))
      (Flat.encodeRowPair stateCoverage symbolCoverage before after)
      accepted)

record PlacedConcreteWindowCNFReceipt
    (machine : Local.ConcreteTapeMachine) : Set₁ where
  field
    stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine)
    symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine)

    flatAssignmentPaid : Bool
    exactFinPlacementPaid : Bool
    pullbackSameObjectPaid : Bool
    placedTruthTableCNFPaid : Bool
    semanticIffPlacedCNFPaid : Bool
    allWindowsConjunctionPaid : Bool
    endpointClausePlacementPaid : Bool
    acceptingRunIffSATPaid : Bool
    polynomialManyOneReductionPaid : Bool
    pVsNPResolved : Bool

canonicalPlacedConcreteWindowCNFReceipt :
  ∀ (machine : Local.ConcreteTapeMachine)
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine)) →
  PlacedConcreteWindowCNFReceipt machine
canonicalPlacedConcreteWindowCNFReceipt machine stateCoverage symbolCoverage = record
  { stateCoverage = stateCoverage
  ; symbolCoverage = symbolCoverage
  ; flatAssignmentPaid = true
  ; exactFinPlacementPaid = true
  ; pullbackSameObjectPaid = true
  ; placedTruthTableCNFPaid = true
  ; semanticIffPlacedCNFPaid = true
  ; allWindowsConjunctionPaid = false
  ; endpointClausePlacementPaid = false
  ; acceptingRunIffSATPaid = false
  ; polynomialManyOneReductionPaid = false
  ; pVsNPResolved = false
  }
