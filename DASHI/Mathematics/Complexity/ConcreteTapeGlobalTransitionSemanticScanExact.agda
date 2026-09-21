module DASHI.Mathematics.Complexity.ConcreteTapeGlobalTransitionSemanticScanExact where

------------------------------------------------------------------------
-- GLOBAL TRANSITION CNF -> SEMANTIC LEGALITY AT EVERY (TIME, WINDOW) SLOT
--
-- This lifts the arbitrary-bit local reflection theorem through the exact
-- recursive lists used by the global conjunction compiler.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Product using (_×_; _,_)

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeCanonicalCellBitsExact as Canonical
import DASHI.Mathematics.Complexity.ConcreteTapeRuleSelectorExact as Selector
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalTraceDecodeExact as Trace
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalTracePlacementExact as Global
import DASHI.Mathematics.Complexity.ConcreteTapeRawGlobalWindowCNFExact as Raw
import DASHI.Mathematics.Complexity.ConcreteTapeArbitrarySelectedWindowSemanticExact as Semantic
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalTransitionConjunctionExact as Transition
import DASHI.Mathematics.Complexity.CNFPlacedConstraintConjunctionExact as Placed
import DASHI.Mathematics.Complexity.FixedWidthTruthTableCNFExact as CNF

------------------------------------------------------------------------
-- Generic conjunction split over the same append used by the compiler
------------------------------------------------------------------------

splitAllPlacedAppend :
  ∀ {local global}
    {assignment : CNF.Bits global}
    (left right : List (Placed.PlacedPredicate local global)) →
  Placed.AllPlacedSatisfied assignment
    (Transition.appendPredicates left right) →
  Placed.AllPlacedSatisfied assignment left
  ×
  Placed.AllPlacedSatisfied assignment right
splitAllPlacedAppend [] right all =
  Placed.allPlacedDone , all
splitAllPlacedAppend (x ∷ xs) right
    (Placed.allPlacedStep current remainder)
    with splitAllPlacedAppend xs right remainder
... | leftRest , rightProof =
  Placed.allPlacedStep current leftRest , rightProof

------------------------------------------------------------------------
-- One time slice: every enumerated column window is semantically legal
------------------------------------------------------------------------

data AllRawWindowsSemantic
    {machine : Local.ConcreteTapeMachine}
    {steps cols timeIndex : Nat}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (timeSlot : Global.Slot timeIndex steps)
    (globalBits : CNF.Bits (Trace.GlobalTraceWidth machine steps cols)) :
    List (Transition.SomeWindowStart cols) → Set where

  semanticWindowsDone :
    AllRawWindowsSemantic
      stateCoverage symbolCoverage nonempty
      timeSlot globalBits []

  semanticWindowsStep :
    ∀ {columnIndex}
      {start : Raw.WindowStart columnIndex cols}
      {rest : List (Transition.SomeWindowStart cols)} →
    Semantic.RawDecodedWindowSemantic
      stateCoverage symbolCoverage nonempty
      timeSlot start globalBits →
    AllRawWindowsSemantic
      stateCoverage symbolCoverage nonempty
      timeSlot globalBits rest →
    AllRawWindowsSemantic
      stateCoverage symbolCoverage nonempty
      timeSlot globalBits
      (Transition.some-window-start columnIndex start ∷ rest)

oneTimePlacedToSemantic :
  ∀ {machine steps cols timeIndex}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (timeSlot : Global.Slot timeIndex steps)
    (starts : List (Transition.SomeWindowStart cols))
    (globalBits : CNF.Bits (Trace.GlobalTraceWidth machine steps cols)) →
  Placed.AllPlacedSatisfied globalBits
    (Transition.predicatesForOneTime
      stateCoverage symbolCoverage nonempty timeSlot starts) →
  AllRawWindowsSemantic
    stateCoverage symbolCoverage nonempty
    timeSlot globalBits starts
oneTimePlacedToSemantic
    stateCoverage symbolCoverage nonempty
    timeSlot [] globalBits Placed.allPlacedDone =
  semanticWindowsDone
oneTimePlacedToSemantic
    stateCoverage symbolCoverage nonempty
    timeSlot
    (Transition.some-window-start columnIndex start ∷ rest)
    globalBits
    (Placed.allPlacedStep current remainder) =
  semanticWindowsStep
    (Semantic.rawSelectedPredicateTrueImpliesSemantic
      stateCoverage symbolCoverage nonempty
      timeSlot start globalBits current)
    (oneTimePlacedToSemantic
      stateCoverage symbolCoverage nonempty
      timeSlot rest globalBits remainder)

------------------------------------------------------------------------
-- All time slices
------------------------------------------------------------------------

data AllTimesSemantic
    {machine : Local.ConcreteTapeMachine}
    {steps cols : Nat}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (globalBits : CNF.Bits (Trace.GlobalTraceWidth machine steps cols)) :
    List (Transition.SomeSlot steps) → Set where

  semanticTimesDone :
    AllTimesSemantic
      stateCoverage symbolCoverage nonempty globalBits []

  semanticTimesStep :
    ∀ {timeIndex}
      {timeSlot : Global.Slot timeIndex steps}
      {rest : List (Transition.SomeSlot steps)} →
    AllRawWindowsSemantic
      stateCoverage symbolCoverage nonempty
      timeSlot globalBits
      (Transition.allWindowStarts cols) →
    AllTimesSemantic
      stateCoverage symbolCoverage nonempty globalBits rest →
    AllTimesSemantic
      stateCoverage symbolCoverage nonempty globalBits
      (Transition.some-slot timeIndex timeSlot ∷ rest)

allTimesPlacedToSemantic :
  ∀ {machine steps cols}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (times : List (Transition.SomeSlot steps))
    (globalBits : CNF.Bits (Trace.GlobalTraceWidth machine steps cols)) →
  Placed.AllPlacedSatisfied globalBits
    (Transition.predicatesForAllTimes
      stateCoverage symbolCoverage nonempty times) →
  AllTimesSemantic
    stateCoverage symbolCoverage nonempty globalBits times
allTimesPlacedToSemantic
    stateCoverage symbolCoverage nonempty
    [] globalBits Placed.allPlacedDone =
  semanticTimesDone
allTimesPlacedToSemantic
    stateCoverage symbolCoverage nonempty
    (Transition.some-slot timeIndex timeSlot ∷ rest)
    globalBits allSatisfied
    with splitAllPlacedAppend
      (Transition.predicatesForOneTime
        stateCoverage symbolCoverage nonempty timeSlot
        (Transition.allWindowStarts _))
      (Transition.predicatesForAllTimes
        stateCoverage symbolCoverage nonempty rest)
      allSatisfied
... | currentTime , remainingTimes =
  semanticTimesStep
    (oneTimePlacedToSemantic
      stateCoverage symbolCoverage nonempty
      timeSlot (Transition.allWindowStarts _)
      globalBits currentTime)
    (allTimesPlacedToSemantic
      stateCoverage symbolCoverage nonempty
      rest globalBits remainingTimes)

record GlobalTransitionSemanticScan
    {machine : Local.ConcreteTapeMachine}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (steps cols : Nat)
    (globalBits : CNF.Bits (Trace.GlobalTraceWidth machine steps cols)) : Set where
  field
    everyTimeEveryWindowSemantic :
      AllTimesSemantic
        stateCoverage symbolCoverage nonempty globalBits
        (Transition.allSlots steps)

open GlobalTransitionSemanticScan public

globalTransitionCNF_to_semanticScan :
  ∀ {machine}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (steps cols : Nat)
    (globalBits : CNF.Bits (Trace.GlobalTraceWidth machine steps cols)) →
  CNF.evaluateCNF
    (Transition.globalTransitionCNF
      stateCoverage symbolCoverage nonempty steps cols)
    globalBits
  ≡ true →
  GlobalTransitionSemanticScan
    stateCoverage symbolCoverage nonempty
    steps cols globalBits
globalTransitionCNF_to_semanticScan
    stateCoverage symbolCoverage nonempty
    steps cols globalBits accepted =
  record
    { everyTimeEveryWindowSemantic =
        allTimesPlacedToSemantic
          stateCoverage symbolCoverage nonempty
          (Transition.allSlots steps)
          globalBits
          (Transition.globalTransitionCNF_sound
            stateCoverage symbolCoverage nonempty
            steps cols globalBits accepted)
    }


------------------------------------------------------------------------
-- Converse: semantic scan -> placed predicates -> global transition CNF
------------------------------------------------------------------------

oneTimeSemanticToPlaced :
  ∀ {machine steps cols timeIndex}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (timeSlot : Global.Slot timeIndex steps)
    (starts : List (Transition.SomeWindowStart cols))
    (globalBits : CNF.Bits (Trace.GlobalTraceWidth machine steps cols)) →
  AllRawWindowsSemantic
    stateCoverage symbolCoverage nonempty
    timeSlot globalBits starts →
  Placed.AllPlacedSatisfied globalBits
    (Transition.predicatesForOneTime
      stateCoverage symbolCoverage nonempty timeSlot starts)
oneTimeSemanticToPlaced
    stateCoverage symbolCoverage nonempty
    timeSlot [] globalBits semanticWindowsDone =
  Placed.allPlacedDone
oneTimeSemanticToPlaced
    stateCoverage symbolCoverage nonempty
    timeSlot
    (Transition.some-window-start columnIndex start ∷ rest)
    globalBits
    (semanticWindowsStep current remaining) =
  Placed.allPlacedStep currentTrue
    (oneTimeSemanticToPlaced
      stateCoverage symbolCoverage nonempty
      timeSlot rest globalBits remaining)
  where
    decodedLegal :
      DASHI.Mathematics.Complexity.ConcreteTapeLocalWindowPatternsExact.LegalWindowForRule
        machine
        (Semantic.decodedSelectedRule nonempty
          (Raw.rawSelectedWindowBits timeSlot start globalBits))
        (Semantic.decodedSelectedWindow
          stateCoverage symbolCoverage
          (Raw.rawSelectedWindowBits timeSlot start globalBits))
    decodedLegal
      rewrite sym (Semantic.ruleExact current)
            | sym (Semantic.windowExact current) =
      Semantic.legal current

    currentTrue :
      Placed.predicate
        (Raw.rawSelectedWindowPlacedPredicate
          stateCoverage symbolCoverage nonempty timeSlot start)
        (DASHI.Mathematics.Complexity.CNFVariableRenamingExact.pullbackBits
          (Placed.rename
            (Raw.rawSelectedWindowPlacedPredicate
              stateCoverage symbolCoverage nonempty timeSlot start))
          globalBits)
      ≡ true
    currentTrue =
      Semantic.decodedSemanticLegalImpliesSelectedPredicateTrue
        stateCoverage symbolCoverage nonempty
        (Raw.rawSelectedWindowBits timeSlot start globalBits)
        decodedLegal

allTimesSemanticToPlaced :
  ∀ {machine steps cols}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (times : List (Transition.SomeSlot steps))
    (globalBits : CNF.Bits (Trace.GlobalTraceWidth machine steps cols)) →
  AllTimesSemantic
    stateCoverage symbolCoverage nonempty globalBits times →
  Placed.AllPlacedSatisfied globalBits
    (Transition.predicatesForAllTimes
      stateCoverage symbolCoverage nonempty times)
allTimesSemanticToPlaced
    stateCoverage symbolCoverage nonempty
    [] globalBits semanticTimesDone =
  Placed.allPlacedDone
allTimesSemanticToPlaced
    stateCoverage symbolCoverage nonempty
    (Transition.some-slot timeIndex timeSlot ∷ rest)
    globalBits
    (semanticTimesStep current remaining) =
  merge
    (oneTimeSemanticToPlaced
      stateCoverage symbolCoverage nonempty
      timeSlot (Transition.allWindowStarts _)
      globalBits current)
    (allTimesSemanticToPlaced
      stateCoverage symbolCoverage nonempty
      rest globalBits remaining)
  where
    merge :
      ∀ {local global}
        {assignment : CNF.Bits global}
        {left right : List (Placed.PlacedPredicate local global)} →
      Placed.AllPlacedSatisfied assignment left →
      Placed.AllPlacedSatisfied assignment right →
      Placed.AllPlacedSatisfied assignment
        (Transition.appendPredicates left right)
    merge Placed.allPlacedDone rightProof =
      rightProof
    merge (Placed.allPlacedStep head tail) rightProof =
      Placed.allPlacedStep head (merge tail rightProof)

semanticScan_to_globalTransitionCNF :
  ∀ {machine}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (steps cols : Nat)
    (globalBits : CNF.Bits (Trace.GlobalTraceWidth machine steps cols)) →
  GlobalTransitionSemanticScan
    stateCoverage symbolCoverage nonempty
    steps cols globalBits →
  CNF.evaluateCNF
    (Transition.globalTransitionCNF
      stateCoverage symbolCoverage nonempty steps cols)
    globalBits
  ≡ true
semanticScan_to_globalTransitionCNF
    stateCoverage symbolCoverage nonempty
    steps cols globalBits semantic =
  Transition.globalTransitionCNF_complete
    stateCoverage symbolCoverage nonempty
    steps cols globalBits
    (allTimesSemanticToPlaced
      stateCoverage symbolCoverage nonempty
      (Transition.allSlots steps)
      globalBits
      (everyTimeEveryWindowSemantic semantic))

record GlobalTransitionSemanticScanReceipt
    (machine : Local.ConcreteTapeMachine) : Set₁ where
  field
    conjunctionAppendSplitPaid : Bool
    oneTimeAllWindowsSemanticPaid : Bool
    allTimesAllWindowsSemanticPaid : Bool
    globalCNFToSemanticScanPaid : Bool
    semanticScanMatchesDecodedRowsPaid : Bool
    semanticScanToWellFormedStepsPaid : Bool
    satToRunPaid : Bool

globalTransitionSemanticScanReceipt :
  ∀ (machine : Local.ConcreteTapeMachine) →
  GlobalTransitionSemanticScanReceipt machine
globalTransitionSemanticScanReceipt machine = record
  { conjunctionAppendSplitPaid = true
  ; oneTimeAllWindowsSemanticPaid = true
  ; allTimesAllWindowsSemanticPaid = true
  ; globalCNFToSemanticScanPaid = true
  ; semanticScanMatchesDecodedRowsPaid = false
  ; semanticScanToWellFormedStepsPaid = false
  ; satToRunPaid = false
  }
