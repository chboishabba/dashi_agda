module DASHI.Mathematics.Complexity.ConcreteTapeWholeRowLocalityExact where

------------------------------------------------------------------------
-- RECURSIVE WHOLE-ROW LOCALITY FOR A CONCRETE ONE-TAPE MACHINE
--
-- The scanner emits every aligned sliding 2x3 window of a pair of rows.
-- For a well-formed contiguous rewrite, every emitted window belongs to the
-- exact directional grammar in ConcreteTapeLocalWindowPatternsExact.
--
-- This pays the forward half of Cook--Levin locality globally, not merely at
-- the distinguished head window.  The reverse global reconstruction theorem
-- remains separate and fail-closed.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeLocalWindowPatternsExact as Pattern
import DASHI.Mathematics.Complexity.ConcreteTapeWellFormedConfigurationExact as WF
import DASHI.Mathematics.Complexity.ConcreteTapeOccurrenceCoordinateExact as Coordinate

data All {A : Set} (Predicate : A → Set) : List A → Set where
  allNil :
    All Predicate []

  allCons :
    ∀ {x xs} →
    Predicate x →
    All Predicate xs →
    All Predicate (x ∷ xs)

scanWindowsCells :
  (machine : Local.ConcreteTapeMachine) →
  List (Local.TapeCell (Local.State machine) (Local.Symbol machine)) →
  List (Local.TapeCell (Local.State machine) (Local.Symbol machine)) →
  List (Local.SixCellWindow machine)
scanWindowsCells machine
    (oldLeft ∷ oldCenter ∷ oldRight ∷ oldRest)
    (newLeft ∷ newCenter ∷ newRight ∷ newRest) =
  Local.six-cell-window
    oldLeft oldCenter oldRight
    newLeft newCenter newRight
  ∷ scanWindowsCells machine
      (oldCenter ∷ oldRight ∷ oldRest)
      (newCenter ∷ newRight ∷ newRest)
scanWindowsCells machine _ _ = []

scanWindows :
  (machine : Local.ConcreteTapeMachine) →
  Local.TapeRow machine →
  Local.TapeRow machine →
  List (Local.SixCellWindow machine)
scanWindows machine before after =
  scanWindowsCells machine
    (Local.cells before)
    (Local.cells after)

AllWindowsLegal :
  (machine : Local.ConcreteTapeMachine) →
  Local.TapeRule (Local.State machine) (Local.Symbol machine) →
  Local.TapeRow machine →
  Local.TapeRow machine →
  Set
AllWindowsLegal machine rule before after =
  All
    (Pattern.LegalWindowForRule machine rule)
    (scanWindows machine before after)

unchangedScanLegal :
  ∀ {machine rule}
    (cells :
      List (Local.TapeCell
        (Local.State machine)
        (Local.Symbol machine))) →
  All
    (Pattern.LegalWindowForRule machine rule)
    (scanWindowsCells machine cells cells)
unchangedScanLegal [] = allNil
unchangedScanLegal (_ ∷ []) = allNil
unchangedScanLegal (_ ∷ _ ∷ []) = allNil
unchangedScanLegal (first ∷ second ∷ third ∷ rest) =
  allCons
    Pattern.legal-unchanged
    (unchangedScanLegal (second ∷ third ∷ rest))

centerRewriteScanLegal :
  ∀ {machine rule window}
    (suffix :
      List (Local.TapeCell
        (Local.State machine)
        (Local.Symbol machine))) →
  WF.PlainCells suffix →
  (configured : Local.RuleRealizesWindow machine rule window) →
  All
    (Pattern.LegalWindowForRule machine rule)
    (scanWindowsCells machine
      (Local.oldLeft window
        ∷ Local.oldCenter window
        ∷ Local.oldRight window
        ∷ suffix)
      (Local.newLeft window
        ∷ Local.newCenter window
        ∷ Local.newRight window
        ∷ suffix))

centerRewriteScanLegal suffix WF.plainNil Local.realizes-left =
  allCons
    (Pattern.legal-centered Local.realizes-left)
    allNil

centerRewriteScanLegal
    (Local.plain next ∷ rest)
    (WF.plainCons restPlain)
    (Local.realizes-left {rightSymbol = rightSymbol}) =
  allCons
    (Pattern.legal-centered Local.realizes-left)
    (allCons
      Pattern.left-overlap-plus-one
      (unchangedScanLegal
        (Local.plain rightSymbol ∷ Local.plain next ∷ rest)))

centerRewriteScanLegal suffix WF.plainNil Local.realizes-stay =
  allCons
    (Pattern.legal-centered Local.realizes-stay)
    allNil

centerRewriteScanLegal
    (Local.plain next ∷ rest)
    (WF.plainCons restPlain)
    (Local.realizes-stay {rightSymbol = rightSymbol}) =
  allCons
    (Pattern.legal-centered Local.realizes-stay)
    (allCons
      Pattern.stay-overlap-plus-one
      (unchangedScanLegal
        (Local.plain rightSymbol ∷ Local.plain next ∷ rest)))

centerRewriteScanLegal suffix WF.plainNil Local.realizes-right =
  allCons
    (Pattern.legal-centered Local.realizes-right)
    allNil

centerRewriteScanLegal
    (Local.plain next ∷ [])
    (WF.plainCons WF.plainNil)
    Local.realizes-right =
  allCons
    (Pattern.legal-centered Local.realizes-right)
    (allCons
      Pattern.right-overlap-plus-one
      allNil)

centerRewriteScanLegal
    (Local.plain next ∷ Local.plain nextTwo ∷ rest)
    (WF.plainCons (WF.plainCons restPlain))
    Local.realizes-right =
  allCons
    (Pattern.legal-centered Local.realizes-right)
    (allCons
      Pattern.right-overlap-plus-one
      (allCons
        Pattern.right-overlap-plus-two
        (unchangedScanLegal
          (Local.plain next ∷ Local.plain nextTwo ∷ rest))))

rewriteScanLegal :
  ∀ {machine rule window}
    (prefix suffix :
      List (Local.TapeCell
        (Local.State machine)
        (Local.Symbol machine))) →
  WF.PlainCells prefix →
  WF.PlainCells suffix →
  (configured : Local.RuleRealizesWindow machine rule window) →
  All
    (Pattern.LegalWindowForRule machine rule)
    (scanWindowsCells machine
      (Local.append prefix
        (Local.oldLeft window
          ∷ Local.oldCenter window
          ∷ Local.oldRight window
          ∷ suffix))
      (Local.append prefix
        (Local.newLeft window
          ∷ Local.newCenter window
          ∷ Local.newRight window
          ∷ suffix)))

rewriteScanLegal [] suffix WF.plainNil suffixPlain configured =
  centerRewriteScanLegal suffix suffixPlain configured

rewriteScanLegal
    (Local.plain prefixOne ∷ [])
    suffix
    (WF.plainCons WF.plainNil)
    suffixPlain
    Local.realizes-left =
  allCons
    Pattern.left-overlap-minus-one
    (centerRewriteScanLegal suffix suffixPlain Local.realizes-left)

rewriteScanLegal
    (Local.plain prefixOne ∷ [])
    suffix
    (WF.plainCons WF.plainNil)
    suffixPlain
    Local.realizes-stay =
  allCons
    Pattern.stay-overlap-minus-one
    (centerRewriteScanLegal suffix suffixPlain Local.realizes-stay)

rewriteScanLegal
    (Local.plain prefixOne ∷ [])
    suffix
    (WF.plainCons WF.plainNil)
    suffixPlain
    Local.realizes-right =
  allCons
    Pattern.right-overlap-minus-one
    (centerRewriteScanLegal suffix suffixPlain Local.realizes-right)

rewriteScanLegal
    (Local.plain prefixOne ∷ Local.plain prefixTwo ∷ [])
    suffix
    (WF.plainCons (WF.plainCons WF.plainNil))
    suffixPlain
    Local.realizes-left =
  allCons
    Pattern.left-overlap-minus-two
    (rewriteScanLegal
      (Local.plain prefixTwo ∷ [])
      suffix
      (WF.plainCons WF.plainNil)
      suffixPlain
      Local.realizes-left)

rewriteScanLegal
    (Local.plain prefixOne ∷ Local.plain prefixTwo ∷ [])
    suffix
    (WF.plainCons (WF.plainCons WF.plainNil))
    suffixPlain
    Local.realizes-stay =
  allCons
    Pattern.legal-unchanged
    (rewriteScanLegal
      (Local.plain prefixTwo ∷ [])
      suffix
      (WF.plainCons WF.plainNil)
      suffixPlain
      Local.realizes-stay)

rewriteScanLegal
    (Local.plain prefixOne ∷ Local.plain prefixTwo ∷ [])
    suffix
    (WF.plainCons (WF.plainCons WF.plainNil))
    suffixPlain
    Local.realizes-right =
  allCons
    Pattern.legal-unchanged
    (rewriteScanLegal
      (Local.plain prefixTwo ∷ [])
      suffix
      (WF.plainCons WF.plainNil)
      suffixPlain
      Local.realizes-right)

rewriteScanLegal
    (Local.plain prefixOne
      ∷ Local.plain prefixTwo
      ∷ Local.plain prefixThree
      ∷ prefixRest)
    suffix
    (WF.plainCons
      (WF.plainCons
        (WF.plainCons prefixRestPlain)))
    suffixPlain
    configured =
  allCons
    Pattern.legal-unchanged
    (rewriteScanLegal
      (Local.plain prefixTwo
        ∷ Local.plain prefixThree
        ∷ prefixRest)
      suffix
      (WF.plainCons
        (WF.plainCons prefixRestPlain))
      suffixPlain
      configured)

transportAllWindowsLegal :
  ∀ {machine rule before after beforeCells afterCells} →
  Local.cells before ≡ beforeCells →
  Local.cells after ≡ afterCells →
  All
    (Pattern.LegalWindowForRule machine rule)
    (scanWindowsCells machine beforeCells afterCells) →
  AllWindowsLegal machine rule before after
transportAllWindowsLegal refl refl proof = proof

machineStepImpliesAllWindowsLegal :
  ∀ {machine before after} →
  (wellFormed : WF.WellFormedMachineStep machine before after) →
  AllWindowsLegal
    machine
    (Local.rule (WF.step wellFormed))
    before
    after
machineStepImpliesAllWindowsLegal wellFormed =
  transportAllWindowsLegal
    (Local.beforeShape occurrenceWitness)
    (Local.afterShape occurrenceWitness)
    (rewriteScanLegal
      (Local.prefix occurrenceWitness)
      (Local.suffix occurrenceWitness)
      (WF.prefixPlain wellFormedOccurrenceWitness)
      (WF.suffixPlain wellFormedOccurrenceWitness)
      (Local.ruleIsConfigured (WF.step wellFormed)))
  where
    wellFormedOccurrenceWitness =
      WF.wellFormedOccurrence wellFormed

    occurrenceWitness =
      WF.occurrence wellFormedOccurrenceWitness


------------------------------------------------------------------------
-- A reverse characterization must exclude the degenerate all-unchanged scan.
-- Therefore global transition locality is "all windows legal" PLUS an actual
-- centered rule window occurring somewhere in the scan.
------------------------------------------------------------------------

data ContainsCenteredRuleWindow
    (machine : Local.ConcreteTapeMachine)
    (rule : Local.TapeRule
      (Local.State machine)
      (Local.Symbol machine)) :
    List (Local.SixCellWindow machine) → Set where

  centeredHere :
    ∀ {window rest} →
    Local.RuleRealizesWindow machine rule window →
    ContainsCenteredRuleWindow machine rule (window ∷ rest)

  centeredThere :
    ∀ {window rest} →
    ContainsCenteredRuleWindow machine rule rest →
    ContainsCenteredRuleWindow machine rule (window ∷ rest)

centeredWindowOccursInRewriteScan :
  ∀ {machine rule window}
    (prefix suffix :
      List (Local.TapeCell
        (Local.State machine)
        (Local.Symbol machine))) →
  WF.PlainCells prefix →
  (configured : Local.RuleRealizesWindow machine rule window) →
  ContainsCenteredRuleWindow machine rule
    (scanWindowsCells machine
      (Local.append prefix
        (Local.oldLeft window
          ∷ Local.oldCenter window
          ∷ Local.oldRight window
          ∷ suffix))
      (Local.append prefix
        (Local.newLeft window
          ∷ Local.newCenter window
          ∷ Local.newRight window
          ∷ suffix)))
centeredWindowOccursInRewriteScan [] suffix WF.plainNil configured =
  centeredHere configured
centeredWindowOccursInRewriteScan
    (Local.plain symbol ∷ prefix)
    suffix
    (WF.plainCons prefixPlain)
    configured =
  centeredThere
    (centeredWindowOccursInRewriteScan
      prefix suffix prefixPlain configured)


rewriteOccurrencePreservesLength :
  ∀ {machine before after window} →
  (occurrence : Local.WindowRewriteOccurrence machine before after window) →
  Coordinate.listLength (Local.cells before)
  ≡ Coordinate.listLength (Local.cells after)
rewriteOccurrencePreservesLength occurrence =
  trans
    (congLength (Local.beforeShape occurrence))
    (sym (congLength (Local.afterShape occurrence)))
  where
    congLength :
      ∀ {A : Set} {xs ys : List A} →
      xs ≡ ys →
      Coordinate.listLength xs ≡ Coordinate.listLength ys
    congLength refl = refl

    sym :
      ∀ {A : Set} {x y : A} →
      x ≡ y → y ≡ x
    sym refl = refl

    trans :
      ∀ {A : Set} {x y z : A} →
      x ≡ y → y ≡ z → x ≡ z
    trans refl second = second

record GlobalTransitionScan
    (machine : Local.ConcreteTapeMachine)
    (rule : Local.TapeRule
      (Local.State machine)
      (Local.Symbol machine))
    (before after : Local.TapeRow machine) : Set where
  field
    ruleOccursInMachine :
      Local.RuleOccurs rule (Local.rules machine)

    sameRowLength :
      Coordinate.listLength (Local.cells before)
      ≡ Coordinate.listLength (Local.cells after)

    everyWindowLegal :
      AllWindowsLegal machine rule before after

    centeredTransitionOccurs :
      ContainsCenteredRuleWindow machine rule
        (scanWindows machine before after)

open GlobalTransitionScan public

transportContainsCentered :
  ∀ {machine rule before after beforeCells afterCells} →
  Local.cells before ≡ beforeCells →
  Local.cells after ≡ afterCells →
  ContainsCenteredRuleWindow machine rule
    (scanWindowsCells machine beforeCells afterCells) →
  ContainsCenteredRuleWindow machine rule
    (scanWindows machine before after)
transportContainsCentered refl refl proof = proof

machineStepImpliesGlobalTransitionScan :
  ∀ {machine before after} →
  (wellFormed : WF.WellFormedMachineStep machine before after) →
  GlobalTransitionScan
    machine
    (Local.rule (WF.step wellFormed))
    before
    after
machineStepImpliesGlobalTransitionScan wellFormed = record
  { ruleOccursInMachine =
      Local.ruleOccursInMachine (WF.step wellFormed)
  ; sameRowLength =
      rewriteOccurrencePreservesLength occurrenceWitness
  ; everyWindowLegal =
      machineStepImpliesAllWindowsLegal wellFormed
  ; centeredTransitionOccurs =
      transportContainsCentered
        (Local.beforeShape occurrenceWitness)
        (Local.afterShape occurrenceWitness)
        (centeredWindowOccursInRewriteScan
          (Local.prefix occurrenceWitness)
          (Local.suffix occurrenceWitness)
          (WF.prefixPlain wellFormedOccurrenceWitness)
          (Local.ruleIsConfigured (WF.step wellFormed)))
  }
  where
    wellFormedOccurrenceWitness =
      WF.wellFormedOccurrence wellFormed

    occurrenceWitness =
      WF.occurrence wellFormedOccurrenceWitness

record ConcreteTapeWholeRowLocalityBoundary : Set where
  constructor concrete-tape-whole-row-locality-boundary
  field
    recursiveWholeRowScanPaid : Bool
    unchangedRegionScanPaid : Bool
    directionalOverlapScanPaid : Bool
    wellFormedStepImpliesAllWindowsPaid : Bool
    centeredTransitionOccurrencePaid : Bool
    equalRowLengthInvariantPaid : Bool
    wellFormedStepImpliesGlobalTransitionScanPaid : Bool
    globalTransitionScanToUniqueRewritePaid : Bool
    legalWindowBooleanReflectionPaid : Bool
    canonicalSATWeldPaid : Bool
    runToSATPaid : Bool
    satToRunPaid : Bool
    genericCookLevinPaid : Bool
    pVsNPResolved : Bool

canonicalConcreteTapeWholeRowLocalityBoundary :
  ConcreteTapeWholeRowLocalityBoundary
canonicalConcreteTapeWholeRowLocalityBoundary =
  concrete-tape-whole-row-locality-boundary
    true true true true true true true false false false false false false false
