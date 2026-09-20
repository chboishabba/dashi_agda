module DASHI.Mathematics.Complexity.ConcreteTapeSelectedRuleWindowCNFExact where

------------------------------------------------------------------------
-- SHARED RULE SELECTOR + INDEXED WINDOW -> ONE PLACED TRANSITION PREDICATE
--
-- Global transition assignment:
--
--   selectorBits ++ encodeRowPair before after
--
-- Every local constraint pulls back:
--
--   selectorBits ++ canonicalWindowBits
--
-- so all windows in a row transition see the same decoded machine rule.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Relation.Binary.PropositionalEquality using (trans; sym)

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeIndexedWindowExact as Indexed
import DASHI.Mathematics.Complexity.ConcreteTapeCanonicalCellBitsExact as Canonical
import DASHI.Mathematics.Complexity.ConcreteTapeFlatAssignmentExact as Flat
import DASHI.Mathematics.Complexity.ConcreteTapeCanonicalWindowPlacementExact as Placement
import DASHI.Mathematics.Complexity.ConcreteTapeRuleSelectorExact as Selector
import DASHI.Mathematics.Complexity.ConcreteTapeWindowCodecCNFWeldExact as Window
import DASHI.Mathematics.Complexity.ConcreteTapeLegalWindowReflectionExact as Reflect
import DASHI.Mathematics.Complexity.ConcreteTapeLocalWindowPatternsExact as Pattern
import DASHI.Mathematics.Complexity.CNFPlacedConstraintConjunctionExact as Placed
import DASHI.Mathematics.Complexity.CNFVariableRenamingExact as Rename
import DASHI.Mathematics.Complexity.FixedWidthTruthTableCNFExact as CNF

TransitionLocalWidth :
  Local.ConcreteTapeMachine → Nat
TransitionLocalWidth machine =
  Selector.RuleWidth machine + Canonical.WindowWidth machine

TransitionGlobalWidth :
  ∀ {machine} →
  Local.TapeRow machine →
  Local.TapeRow machine →
  Nat
TransitionGlobalWidth {machine} before after =
  Selector.RuleWidth machine + Flat.RowPairWidth before after
selectedRuleWindowPredicateWithCoverage :
  ∀ {machine}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine) →
  CNF.Bits (TransitionLocalWidth machine) →
  Bool
selectedRuleWindowPredicateWithCoverage
    {machine} stateCoverage symbolCoverage nonempty bits =
  Window.encodedWindowPredicate
    (Canonical.canonicalWindowCodec
      machine stateCoverage symbolCoverage)
    (Selector.decodeRule nonempty selectorBits)
    windowBits
  where
    selectorBits =
      Canonical.takeBits
        (Selector.RuleWidth machine)
        bits

    windowBits =
      Canonical.dropBits
        (Selector.RuleWidth machine)
        bits

encodeSelectedRuleWindow :
  ∀ {machine}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    {rule : Local.TapeRule
      (Local.State machine)
      (Local.Symbol machine)} →
  Local.RuleOccurs rule (Local.rules machine) →
  Local.SixCellWindow machine →
  CNF.Bits (TransitionLocalWidth machine)
encodeSelectedRuleWindow stateCoverage symbolCoverage occurrence window =
  Canonical.appendBits
    (Selector.encodeRuleOccurs occurrence)
    (Window.FixedWidthWindowCodec.encode
      (Canonical.canonicalWindowCodec
        _ stateCoverage symbolCoverage)
      window)

selectedRuleWindowPredicate_encode :
  ∀ {machine}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    {rule : Local.TapeRule
      (Local.State machine)
      (Local.Symbol machine)}
    (occurrence : Local.RuleOccurs rule (Local.rules machine))
    (window : Local.SixCellWindow machine) →
  selectedRuleWindowPredicateWithCoverage
    stateCoverage symbolCoverage nonempty
    (encodeSelectedRuleWindow
      stateCoverage symbolCoverage occurrence window)
  ≡ Reflect.reflectedLegalWindowBool machine rule window
selectedRuleWindowPredicate_encode
    stateCoverage symbolCoverage nonempty occurrence window
    rewrite Canonical.takeAppendBits
      (Selector.encodeRuleOccurs occurrence)
      (Window.FixedWidthWindowCodec.encode
        (Canonical.canonicalWindowCodec _ stateCoverage symbolCoverage)
        window)
          | Canonical.dropAppendBits
              (Selector.encodeRuleOccurs occurrence)
              (Window.FixedWidthWindowCodec.encode
                (Canonical.canonicalWindowCodec _ stateCoverage symbolCoverage)
                window)
          | Selector.decodeEncodedRule nonempty occurrence
          | Window.FixedWidthWindowCodec.decodeEncode
              (Canonical.canonicalWindowCodec _ stateCoverage symbolCoverage)
              window =
  refl

semanticSelectedRuleWindowImpliesBoolean :
  ∀ {machine}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    {rule : Local.TapeRule
      (Local.State machine)
      (Local.Symbol machine)}
    (occurrence : Local.RuleOccurs rule (Local.rules machine))
    (window : Local.SixCellWindow machine) →
  Pattern.LegalWindowForRule machine rule window →
  selectedRuleWindowPredicateWithCoverage
    stateCoverage symbolCoverage nonempty
    (encodeSelectedRuleWindow
      stateCoverage symbolCoverage occurrence window)
  ≡ true
semanticSelectedRuleWindowImpliesBoolean
    stateCoverage symbolCoverage nonempty occurrence window legal
    rewrite selectedRuleWindowPredicate_encode
      stateCoverage symbolCoverage nonempty occurrence window =
  Reflect.semanticLegalImpliesReflectedBooleanTrue legal

------------------------------------------------------------------------
-- Global transition assignment and exact local placement
------------------------------------------------------------------------

encodeTransitionAssignment :
  ∀ {machine before after}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    {rule : Local.TapeRule
      (Local.State machine)
      (Local.Symbol machine)} →
  Local.RuleOccurs rule (Local.rules machine) →
  CNF.Bits (TransitionGlobalWidth before after)
encodeTransitionAssignment
    stateCoverage symbolCoverage occurrence =
  Canonical.appendBits
    (Selector.encodeRuleOccurs occurrence)
    (Flat.encodeRowPair stateCoverage symbolCoverage _ _)

selectedIndexedWindowPlacement :
  ∀ {machine before after}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    {rule : Local.TapeRule
      (Local.State machine)
      (Local.Symbol machine)}
    (ruleOccurrence : Local.RuleOccurs rule (Local.rules machine))
    (windowOccurrence :
      Indexed.IndexedSixCellWindow machine before after) →
  Placement.BitsPlacement
    (encodeSelectedRuleWindow
      stateCoverage symbolCoverage ruleOccurrence
      (Indexed.forgetIndex windowOccurrence))
    (encodeTransitionAssignment
      stateCoverage symbolCoverage ruleOccurrence)
selectedIndexedWindowPlacement
    stateCoverage symbolCoverage ruleOccurrence windowOccurrence =
  Placement.appendPlacement selectorPlaced windowPlacedGlobal
  where
    selectorBits = Selector.encodeRuleOccurs ruleOccurrence
    rowPairBits =
      Flat.encodeRowPair stateCoverage symbolCoverage _ _

    selectorPlaced =
      Placement.placementLeft selectorBits rowPairBits

    windowPlacedInPair =
      Placement.indexedWindowBitsPlacement
        stateCoverage symbolCoverage windowOccurrence

    rowPairPlaced =
      Placement.placementRight selectorBits rowPairBits

    windowPlacedGlobal =
      Placement.composePlacement
        windowPlacedInPair
        rowPairPlaced

selectedIndexedWindowRename :
  ∀ {machine before after}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    {rule : Local.TapeRule
      (Local.State machine)
      (Local.Symbol machine)}
    (ruleOccurrence : Local.RuleOccurs rule (Local.rules machine))
    (windowOccurrence :
      Indexed.IndexedSixCellWindow machine before after) →
  Data.Fin.Base.Fin (TransitionLocalWidth machine) →
  Data.Fin.Base.Fin (TransitionGlobalWidth before after)
selectedIndexedWindowRename
    stateCoverage symbolCoverage ruleOccurrence windowOccurrence =
  Placement.rename
    (selectedIndexedWindowPlacement
      stateCoverage symbolCoverage ruleOccurrence windowOccurrence)

selectedIndexedWindowPullback :
  ∀ {machine before after}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    {rule : Local.TapeRule
      (Local.State machine)
      (Local.Symbol machine)}
    (ruleOccurrence : Local.RuleOccurs rule (Local.rules machine))
    (windowOccurrence :
      Indexed.IndexedSixCellWindow machine before after) →
  Rename.pullbackBits
    (selectedIndexedWindowRename
      stateCoverage symbolCoverage ruleOccurrence windowOccurrence)
    (encodeTransitionAssignment
      stateCoverage symbolCoverage ruleOccurrence)
  ≡ encodeSelectedRuleWindow
      stateCoverage symbolCoverage ruleOccurrence
      (Indexed.forgetIndex windowOccurrence)
selectedIndexedWindowPullback
    stateCoverage symbolCoverage ruleOccurrence windowOccurrence =
  Placement.pullbackPlacement
    (selectedIndexedWindowPlacement
      stateCoverage symbolCoverage ruleOccurrence windowOccurrence)

selectedIndexedWindowPlacedPredicate :
  ∀ {machine before after}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    {rule : Local.TapeRule
      (Local.State machine)
      (Local.Symbol machine)}
    (ruleOccurrence : Local.RuleOccurs rule (Local.rules machine))
    (windowOccurrence :
      Indexed.IndexedSixCellWindow machine before after) →
  Placed.PlacedPredicate
    (TransitionLocalWidth machine)
    (TransitionGlobalWidth before after)
selectedIndexedWindowPlacedPredicate
    stateCoverage symbolCoverage nonempty
    ruleOccurrence windowOccurrence =
  Placed.placed-predicate
    (selectedIndexedWindowRename
      stateCoverage symbolCoverage ruleOccurrence windowOccurrence)
    (selectedRuleWindowPredicateWithCoverage
      stateCoverage symbolCoverage nonempty)

selectedPlacedPredicate_true_of_semantic :
  ∀ {machine before after}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    {rule : Local.TapeRule
      (Local.State machine)
      (Local.Symbol machine)}
    (ruleOccurrence : Local.RuleOccurs rule (Local.rules machine))
    (windowOccurrence :
      Indexed.IndexedSixCellWindow machine before after) →
  Pattern.LegalWindowForRule
    machine rule (Indexed.forgetIndex windowOccurrence) →
  Placed.predicate
    (selectedIndexedWindowPlacedPredicate
      stateCoverage symbolCoverage nonempty
      ruleOccurrence windowOccurrence)
    (Rename.pullbackBits
      (Placed.rename
        (selectedIndexedWindowPlacedPredicate
          stateCoverage symbolCoverage nonempty
          ruleOccurrence windowOccurrence))
      (encodeTransitionAssignment
        stateCoverage symbolCoverage ruleOccurrence))
  ≡ true
selectedPlacedPredicate_true_of_semantic
    stateCoverage symbolCoverage nonempty
    ruleOccurrence windowOccurrence legal
    rewrite selectedIndexedWindowPullback
      stateCoverage symbolCoverage ruleOccurrence windowOccurrence =
  semanticSelectedRuleWindowImpliesBoolean
    stateCoverage symbolCoverage nonempty
    ruleOccurrence (Indexed.forgetIndex windowOccurrence) legal

record SharedRuleWindowPlacementReceipt
    (machine : Local.ConcreteTapeMachine) : Set₁ where
  field
    nonemptyRuleTable : Selector.NonemptyRuleTable machine
    selectorBitsPaid : Bool
    selectorDecodesInsideMachinePaid : Bool
    sharedSelectorPlusWindowPredicatePaid : Bool
    transitionGlobalAssignmentPaid : Bool
    exactSelectedWindowPlacementPaid : Bool
    knownStepSatisfiesSelectedPredicatePaid : Bool
    arbitrarySATAssignmentToDecodedRuleScanPaid : Bool
    wholeTransitionCNFIffStepPaid : Bool
    endpointCNFPaid : Bool
    acceptingRunIffSATPaid : Bool
    pVsNPResolved : Bool
