module DASHI.Mathematics.Complexity.ConcreteTapeArbitrarySelectedWindowSemanticExact where

------------------------------------------------------------------------
-- ARBITRARY SAT LOCAL BITS -> ACTUAL SEMANTIC LEGAL WINDOW
--
-- The reduction-facing local predicate is total on arbitrary Boolean blocks:
--
--   selector bits || six cell blocks
--
-- The selector decodes to an actual machine rule and the six cell blocks
-- decode to an actual SixCellWindow.  Boolean truth is reflected all the way
-- back to the proof-carrying semantic LegalWindowForRule proposition.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeCanonicalCellBitsExact as Canonical
import DASHI.Mathematics.Complexity.ConcreteTapeRuleSelectorExact as Selector
import DASHI.Mathematics.Complexity.ConcreteTapeSelectedRuleWindowCNFExact as Selected
import DASHI.Mathematics.Complexity.ConcreteTapeRawGlobalWindowCNFExact as Raw
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalTracePlacementExact as Global
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalTraceDecodeExact as Trace
import DASHI.Mathematics.Complexity.ConcreteTapeWindowCodecCNFWeldExact as Window
import DASHI.Mathematics.Complexity.ConcreteTapeLegalWindowReflectionExact as Reflect
import DASHI.Mathematics.Complexity.ConcreteTapeLocalWindowPatternsExact as Pattern
import DASHI.Mathematics.Complexity.FixedWidthTruthTableCNFExact as CNF

decodedSelectedRule :
  ∀ {machine}
    (nonempty : Selector.NonemptyRuleTable machine) →
  CNF.Bits (Selected.TransitionLocalWidth machine) →
  Local.TapeRule
    (Local.State machine)
    (Local.Symbol machine)
decodedSelectedRule {machine} nonempty bits =
  Selector.decodeRule nonempty
    (Canonical.takeBits
      (Selector.RuleWidth machine)
      bits)

decodedSelectedWindow :
  ∀ {machine}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine)) →
  CNF.Bits (Selected.TransitionLocalWidth machine) →
  Local.SixCellWindow machine
decodedSelectedWindow {machine}
    stateCoverage symbolCoverage bits =
  Window.decode
    (Canonical.canonicalWindowCodec
      machine stateCoverage symbolCoverage)
    (Canonical.dropBits
      (Selector.RuleWidth machine)
      bits)

/--
The local truth-table predicate is semantically sound for arbitrary bits,
not merely for encodings produced from a known machine run.
-/
selectedPredicateTrueImpliesDecodedSemanticLegal :
  ∀ {machine}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (bits : CNF.Bits (Selected.TransitionLocalWidth machine)) →
  Selected.selectedRuleWindowPredicateWithCoverage
    stateCoverage symbolCoverage nonempty bits
  ≡ true →
  Pattern.LegalWindowForRule
    machine
    (decodedSelectedRule nonempty bits)
    (decodedSelectedWindow
      stateCoverage symbolCoverage bits)
selectedPredicateTrueImpliesDecodedSemanticLegal
    {machine} stateCoverage symbolCoverage nonempty bits accepted =
  Reflect.booleanTrueImpliesSemanticLegal accepted

record RawDecodedWindowSemantic
    {machine : Local.ConcreteTapeMachine}
    {steps cols timeIndex columnIndex : Nat}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (timeSlot : Global.Slot timeIndex steps)
    (start : Raw.WindowStart columnIndex cols)
    (globalBits :
      CNF.Bits
        (Trace.GlobalTraceWidth
          machine steps cols)) : Set where
  field
    rule :
      Local.TapeRule
        (Local.State machine)
        (Local.Symbol machine)

    window :
      Local.SixCellWindow machine

    ruleExact :
      rule ≡
        decodedSelectedRule nonempty
          (Raw.rawSelectedWindowBits timeSlot start globalBits)

    windowExact :
      window ≡
        decodedSelectedWindow stateCoverage symbolCoverage
          (Raw.rawSelectedWindowBits timeSlot start globalBits)

    legal :
      Pattern.LegalWindowForRule machine rule window

open RawDecodedWindowSemantic public

/--
Truth of one raw fixed-coordinate predicate now yields an actual semantic
legal six-cell transition window under the actual decoded shared rule.
-/
rawSelectedPredicateTrueImpliesSemantic :
  ∀ {machine steps cols timeIndex columnIndex}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (timeSlot : Global.Slot timeIndex steps)
    (start : Raw.WindowStart columnIndex cols)
    (globalBits :
      CNF.Bits
        (Trace.GlobalTraceWidth
          machine steps cols)) →
  Selected.selectedRuleWindowPredicateWithCoverage
    stateCoverage symbolCoverage nonempty
    (Raw.rawSelectedWindowBits timeSlot start globalBits)
  ≡ true →
  RawDecodedWindowSemantic
    stateCoverage symbolCoverage nonempty
    timeSlot start globalBits
rawSelectedPredicateTrueImpliesSemantic
    stateCoverage symbolCoverage nonempty
    timeSlot start globalBits accepted =
  record
    { rule =
        decodedSelectedRule nonempty localBits
    ; window =
        decodedSelectedWindow
          stateCoverage symbolCoverage localBits
    ; ruleExact = refl
    ; windowExact = refl
    ; legal =
        selectedPredicateTrueImpliesDecodedSemanticLegal
          stateCoverage symbolCoverage nonempty
          localBits accepted
    }
  where
    localBits =
      Raw.rawSelectedWindowBits timeSlot start globalBits

record ArbitrarySelectedWindowSemanticReceipt
    (machine : Local.ConcreteTapeMachine) : Set₁ where
  field
    arbitrarySelectorDecodePaid : Bool
    arbitraryWindowDecodePaid : Bool
    booleanTruthToSemanticLegalityPaid : Bool
    rawCoordinateTruthToSemanticWindowPaid : Bool
    allCoordinatesToWholeRowScanPaid : Bool
    wholeRowScanToStepPaid : Bool
    satToRunPaid : Bool

arbitrarySelectedWindowSemanticReceipt :
  ∀ (machine : Local.ConcreteTapeMachine) →
  ArbitrarySelectedWindowSemanticReceipt machine
arbitrarySelectedWindowSemanticReceipt machine = record
  { arbitrarySelectorDecodePaid = true
  ; arbitraryWindowDecodePaid = true
  ; booleanTruthToSemanticLegalityPaid = true
  ; rawCoordinateTruthToSemanticWindowPaid = true
  ; allCoordinatesToWholeRowScanPaid = Agda.Builtin.Bool.false
  ; wholeRowScanToStepPaid = Agda.Builtin.Bool.false
  ; satToRunPaid = Agda.Builtin.Bool.false
  }
