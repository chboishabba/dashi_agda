module DASHI.Mathematics.Complexity.ConcreteTapePlacedWindowCNFExact where

------------------------------------------------------------------------
-- ACTUAL INDEXED WINDOW -> PLACED LOCAL CNF ON THE FLAT ROW-PAIR ASSIGNMENT
--
-- The preceding placement theorem proves that pulling the global row-pair
-- assignment back along indexedWindowRename gives exactly the canonical
-- six-cell code.  Therefore the generic PlacedPredicate / truth-table CNF
-- compiler can now be instantiated on the actual concrete tape representation.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (subst; sym)

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
indexedWindowPlacedPredicate
    stateCoverage symbolCoverage rule occurrence =
  Placed.placed-predicate
    (Placement.indexedWindowRename
      stateCoverage symbolCoverage occurrence)
    (Window.encodedWindowPredicate
      (Canonical.canonicalWindowCodec
        _ stateCoverage symbolCoverage)
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
    stateCoverage symbolCoverage rule occurrence
    with Placement.indexedWindowPullback_is_canonicalWindowEncoding
      stateCoverage symbolCoverage occurrence
... | refl = refl

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
    stateCoverage symbolCoverage rule occurrence legal
    with indexedWindowPulledPredicate_is_reflectedWindow
      stateCoverage symbolCoverage rule occurrence
... | refl =
  Reflect.semanticLegalImpliesReflectedBooleanTrue legal

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
    stateCoverage symbolCoverage rule occurrence accepted
    with indexedWindowPulledPredicate_is_reflectedWindow
      stateCoverage symbolCoverage rule occurrence
... | refl =
  Reflect.booleanTrueImpliesSemanticLegal accepted

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
semanticLegalIndexedWindowImpliesPlacedCNF
    stateCoverage symbolCoverage rule occurrence legal =
  Placed.compilePlacedAllComplete
    (indexedWindowPlacedPredicate
      stateCoverage symbolCoverage rule occurrence ∷ [])
    (Flat.encodeRowPair stateCoverage symbolCoverage _ _)
    (Placed.allPlacedStep
      (semanticLegalIndexedWindowImpliesPlacedPredicate
        stateCoverage symbolCoverage rule occurrence legal)
      Placed.allPlacedDone)

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
placedCNFImpliesSemanticLegalIndexedWindow
    stateCoverage symbolCoverage rule occurrence accepted =
  placedPredicateImpliesSemanticLegalIndexedWindow
    stateCoverage symbolCoverage rule occurrence
    localAccepted
  where
    allAccepted =
      Placed.compilePlacedAllSound
        (indexedWindowPlacedPredicate
          stateCoverage symbolCoverage rule occurrence ∷ [])
        (Flat.encodeRowPair stateCoverage symbolCoverage _ _)
        accepted

    localAccepted :
      Placed.predicate
        (indexedWindowPlacedPredicate
          stateCoverage symbolCoverage rule occurrence)
        (Rename.pullbackBits
          (Placed.rename
            (indexedWindowPlacedPredicate
              stateCoverage symbolCoverage rule occurrence))
          (Flat.encodeRowPair
            stateCoverage symbolCoverage _ _))
      ≡ true
    localAccepted
      with allAccepted
    ... | Placed.allPlacedStep proof Placed.allPlacedDone = proof

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
