module DASHI.Mathematics.Complexity.ConcreteTapeGlobalTransitionSemanticCompleteExact where

------------------------------------------------------------------------
-- SEMANTIC RAW SCAN -> GLOBAL TRANSITION CNF
--
-- Converse to ConcreteTapeGlobalTransitionSemanticScanExact.
-- No canonicality assumption is needed: RawDecodedWindowSemantic already says
-- exactly what the arbitrary local SAT bits decode to, and that decoded object
-- is semantically legal.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (trans; sym)

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeCanonicalCellBitsExact as Canonical
import DASHI.Mathematics.Complexity.ConcreteTapeRuleSelectorExact as Selector
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalTraceDecodeExact as Trace
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalTracePlacementExact as Global
import DASHI.Mathematics.Complexity.ConcreteTapeRawGlobalWindowCNFExact as Raw
import DASHI.Mathematics.Complexity.ConcreteTapeArbitrarySelectedWindowSemanticExact as Semantic
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalTransitionSemanticScanExact as Scan
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalTransitionConjunctionExact as Transition
import DASHI.Mathematics.Complexity.ConcreteTapeSelectedRuleWindowCNFExact as Selected
import DASHI.Mathematics.Complexity.ConcreteTapeWindowCodecCNFWeldExact as Window
import DASHI.Mathematics.Complexity.ConcreteTapeLegalWindowReflectionExact as Reflect
import DASHI.Mathematics.Complexity.ConcreteTapeLocalWindowPatternsExact as Pattern
import DASHI.Mathematics.Complexity.CNFPlacedConstraintConjunctionExact as Placed
import DASHI.Mathematics.Complexity.CNFVariableRenamingExact as Rename
import DASHI.Mathematics.Complexity.FixedWidthTruthTableCNFExact as CNF

------------------------------------------------------------------------
-- One arbitrary raw semantic witness gives one true placed predicate
------------------------------------------------------------------------

rawSemanticDecodedLegal :
  ∀ {machine steps cols timeIndex columnIndex}
    {stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine)}
    {symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine)}
    {nonempty : Selector.NonemptyRuleTable machine}
    {timeSlot : Global.Slot timeIndex steps}
    {start : Raw.WindowStart columnIndex cols}
    {globalBits : CNF.Bits (Trace.GlobalTraceWidth machine steps cols)}
    (semantic :
      Semantic.RawDecodedWindowSemantic
        stateCoverage symbolCoverage nonempty
        timeSlot start globalBits) →
  Pattern.LegalWindowForRule
    machine
    (Semantic.decodedSelectedRule nonempty
      (Raw.rawSelectedWindowBits timeSlot start globalBits))
    (Semantic.decodedSelectedWindow stateCoverage symbolCoverage
      (Raw.rawSelectedWindowBits timeSlot start globalBits))
rawSemanticDecodedLegal semantic
  rewrite sym (Semantic.ruleExact semantic)
        | sym (Semantic.windowExact semantic) =
  Semantic.legal semantic

rawSemanticImpliesLocalPredicateTrue :
  ∀ {machine steps cols timeIndex columnIndex}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (timeSlot : Global.Slot timeIndex steps)
    (start : Raw.WindowStart columnIndex cols)
    (globalBits : CNF.Bits (Trace.GlobalTraceWidth machine steps cols)) →
  Semantic.RawDecodedWindowSemantic
    stateCoverage symbolCoverage nonempty
    timeSlot start globalBits →
  Selected.selectedRuleWindowPredicateWithCoverage
    stateCoverage symbolCoverage nonempty
    (Raw.rawSelectedWindowBits timeSlot start globalBits)
  ≡ true
rawSemanticImpliesLocalPredicateTrue
    stateCoverage symbolCoverage nonempty
    timeSlot start globalBits semantic =
  Reflect.semanticLegalImpliesReflectedBooleanTrue
    (rawSemanticDecodedLegal semantic)

rawSemanticImpliesPlacedPredicateTrue :
  ∀ {machine steps cols timeIndex columnIndex}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (timeSlot : Global.Slot timeIndex steps)
    (start : Raw.WindowStart columnIndex cols)
    (globalBits : CNF.Bits (Trace.GlobalTraceWidth machine steps cols)) →
  Semantic.RawDecodedWindowSemantic
    stateCoverage symbolCoverage nonempty
    timeSlot start globalBits →
  Placed.predicate
    (Raw.rawSelectedWindowPlacedPredicate
      stateCoverage symbolCoverage nonempty timeSlot start)
    (Rename.pullbackBits
      (Placed.rename
        (Raw.rawSelectedWindowPlacedPredicate
          stateCoverage symbolCoverage nonempty timeSlot start))
      globalBits)
  ≡ true
rawSemanticImpliesPlacedPredicateTrue
    stateCoverage symbolCoverage nonempty
    timeSlot start globalBits semantic =
  rawSemanticImpliesLocalPredicateTrue
    stateCoverage symbolCoverage nonempty
    timeSlot start globalBits semantic

------------------------------------------------------------------------
-- One time slice
------------------------------------------------------------------------

semanticWindowsToPlaced :
  ∀ {machine steps cols timeIndex}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (timeSlot : Global.Slot timeIndex steps)
    (starts : List (Transition.SomeWindowStart cols))
    (globalBits : CNF.Bits (Trace.GlobalTraceWidth machine steps cols)) →
  Scan.AllRawWindowsSemantic
    stateCoverage symbolCoverage nonempty
    timeSlot globalBits starts →
  Placed.AllPlacedSatisfied globalBits
    (Transition.predicatesForOneTime
      stateCoverage symbolCoverage nonempty timeSlot starts)
semanticWindowsToPlaced
    stateCoverage symbolCoverage nonempty
    timeSlot [] globalBits Scan.semanticWindowsDone =
  Placed.allPlacedDone
semanticWindowsToPlaced
    stateCoverage symbolCoverage nonempty
    timeSlot
    (Transition.some-window-start index start ∷ rest)
    globalBits
    (Scan.semanticWindowsStep current remaining) =
  Placed.allPlacedStep
    (rawSemanticImpliesPlacedPredicateTrue
      stateCoverage symbolCoverage nonempty
      timeSlot start globalBits current)
    (semanticWindowsToPlaced
      stateCoverage symbolCoverage nonempty
      timeSlot rest globalBits remaining)

appendAllPlaced :
  ∀ {local global}
    {assignment : CNF.Bits global}
    (left right : List (Placed.PlacedPredicate local global)) →
  Placed.AllPlacedSatisfied assignment left →
  Placed.AllPlacedSatisfied assignment right →
  Placed.AllPlacedSatisfied assignment
    (Transition.appendPredicates left right)
appendAllPlaced [] right Placed.allPlacedDone rightProof =
  rightProof
appendAllPlaced (x ∷ xs) right
    (Placed.allPlacedStep current rest) rightProof =
  Placed.allPlacedStep current
    (appendAllPlaced xs right rest rightProof)

------------------------------------------------------------------------
-- All time slices
------------------------------------------------------------------------

semanticTimesToPlaced :
  ∀ {machine steps cols}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (times : List (Transition.SomeSlot steps))
    (globalBits : CNF.Bits (Trace.GlobalTraceWidth machine steps cols)) →
  Scan.AllTimesSemantic
    stateCoverage symbolCoverage nonempty globalBits times →
  Placed.AllPlacedSatisfied globalBits
    (Transition.predicatesForAllTimes
      stateCoverage symbolCoverage nonempty times)
semanticTimesToPlaced
    stateCoverage symbolCoverage nonempty
    [] globalBits Scan.semanticTimesDone =
  Placed.allPlacedDone
semanticTimesToPlaced
    stateCoverage symbolCoverage nonempty
    (Transition.some-slot timeIndex timeSlot ∷ rest)
    globalBits
    (Scan.semanticTimesStep current remaining) =
  appendAllPlaced
    (Transition.predicatesForOneTime
      stateCoverage symbolCoverage nonempty timeSlot
      (Transition.allWindowStarts _))
    (Transition.predicatesForAllTimes
      stateCoverage symbolCoverage nonempty rest)
    (semanticWindowsToPlaced
      stateCoverage symbolCoverage nonempty
      timeSlot (Transition.allWindowStarts _)
      globalBits current)
    (semanticTimesToPlaced
      stateCoverage symbolCoverage nonempty
      rest globalBits remaining)

globalTransitionCNF_complete_of_semanticScan :
  ∀ {machine}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (steps cols : Nat)
    (globalBits : CNF.Bits (Trace.GlobalTraceWidth machine steps cols)) →
  Scan.AllTimesSemantic
    stateCoverage symbolCoverage nonempty globalBits
    (Transition.allSlots steps) →
  CNF.evaluateCNF
    (Transition.globalTransitionCNF
      stateCoverage symbolCoverage nonempty steps cols)
    globalBits
  ≡ true
globalTransitionCNF_complete_of_semanticScan
    stateCoverage symbolCoverage nonempty
    steps cols globalBits semantic =
  Transition.globalTransitionCNF_complete
    stateCoverage symbolCoverage nonempty
    steps cols globalBits
    (semanticTimesToPlaced
      stateCoverage symbolCoverage nonempty
      (Transition.allSlots steps)
      globalBits semantic)

record GlobalTransitionSemanticCompleteReceipt
    (machine : Local.ConcreteTapeMachine) : Set₁ where
  field
    rawSemanticToLocalPredicatePaid : Bool
    semanticWindowListToPlacedPaid : Bool
    semanticTimeListToPlacedPaid : Bool
    semanticScanToGlobalTransitionCNFPaid : Bool

globalTransitionSemanticCompleteReceipt :
  ∀ (machine : Local.ConcreteTapeMachine) →
  GlobalTransitionSemanticCompleteReceipt machine
globalTransitionSemanticCompleteReceipt machine = record
  { rawSemanticToLocalPredicatePaid = true
  ; semanticWindowListToPlacedPaid = true
  ; semanticTimeListToPlacedPaid = true
  ; semanticScanToGlobalTransitionCNFPaid = true
  }
