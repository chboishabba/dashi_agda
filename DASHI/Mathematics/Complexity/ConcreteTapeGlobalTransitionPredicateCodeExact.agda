module DASHI.Mathematics.Complexity.ConcreteTapeGlobalTransitionPredicateCodeExact where

------------------------------------------------------------------------
-- FINITE CODE FOR EVERY GLOBAL TRANSITION PLACED PREDICATE
--
-- `allGlobalTransitionPredicates` stores function-valued PlacedPredicate records.
-- But every member is generated from finite `(time,column)` coordinates and the
-- SAME fixed local selected-rule/window predicate.  This owner defunctionalizes
-- the varying part to finite proof-bearing coordinate syntax.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeCanonicalCellBitsExact as Canonical
import DASHI.Mathematics.Complexity.ConcreteTapeRuleSelectorExact as Selector
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalTraceDecodeExact as Trace
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalTracePlacementExact as Global
import DASHI.Mathematics.Complexity.ConcreteTapeRawGlobalWindowCNFExact as Raw
import DASHI.Mathematics.Complexity.ConcreteTapeSelectedRuleWindowCNFExact as Selected
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalTransitionConjunctionExact as Transition
import DASHI.Mathematics.Complexity.CNFPlacedConstraintConjunctionExact as Placed

record TransitionPredicateCode (steps cols : Nat) : Set where
  constructor transition-predicate-code
  field
    timeIndex : Nat
    timeSlot : Global.Slot timeIndex steps
    columnIndex : Nat
    windowStart : Raw.WindowStart columnIndex cols

open TransitionPredicateCode public

interpretTransitionPredicateCode :
  ∀ {machine steps cols}
    (stateCoverage : Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage : Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine) →
  TransitionPredicateCode steps cols →
  Placed.PlacedPredicate
    (Selected.TransitionLocalWidth machine)
    (Trace.GlobalTraceWidth machine steps cols)
interpretTransitionPredicateCode
    stateCoverage symbolCoverage nonempty
    (transition-predicate-code timeIndex timeSlot columnIndex start) =
  Raw.rawSelectedWindowPlacedPredicate
    stateCoverage symbolCoverage nonempty timeSlot start

------------------------------------------------------------------------
-- Exact coordinate enumeration mirroring the existing predicate enumeration.
------------------------------------------------------------------------

codesForOneTime :
  ∀ {steps cols timeIndex} →
  Global.Slot timeIndex steps →
  List (Transition.SomeWindowStart cols) →
  List (TransitionPredicateCode steps cols)
codesForOneTime timeSlot [] = []
codesForOneTime timeSlot
    (Transition.some-window-start columnIndex start ∷ rest) =
  transition-predicate-code _ timeSlot columnIndex start
  ∷ codesForOneTime timeSlot rest

appendCodes :
  ∀ {steps cols} →
  List (TransitionPredicateCode steps cols) →
  List (TransitionPredicateCode steps cols) →
  List (TransitionPredicateCode steps cols)
appendCodes [] right = right
appendCodes (x ∷ left) right = x ∷ appendCodes left right

codesForAllTimes :
  ∀ {steps cols} →
  List (Transition.SomeSlot steps) →
  List (TransitionPredicateCode steps cols)
codesForAllTimes [] = []
codesForAllTimes
    (Transition.some-slot timeIndex timeSlot ∷ rest) =
  appendCodes
    (codesForOneTime timeSlot (Transition.allWindowStarts _))
    (codesForAllTimes rest)

allGlobalTransitionCodes :
  (steps cols : Nat) →
  List (TransitionPredicateCode steps cols)
allGlobalTransitionCodes steps cols =
  codesForAllTimes (Transition.allSlots steps)

------------------------------------------------------------------------
-- List interpretation and exact equality to the old higher-order list.
------------------------------------------------------------------------

interpretCodes :
  ∀ {machine steps cols}
    (stateCoverage : Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage : Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine) →
  List (TransitionPredicateCode steps cols) →
  List
    (Placed.PlacedPredicate
      (Selected.TransitionLocalWidth machine)
      (Trace.GlobalTraceWidth machine steps cols))
interpretCodes stateCoverage symbolCoverage nonempty [] = []
interpretCodes stateCoverage symbolCoverage nonempty (code ∷ rest) =
  interpretTransitionPredicateCode
    stateCoverage symbolCoverage nonempty code
  ∷ interpretCodes stateCoverage symbolCoverage nonempty rest

interpretAppendCodes :
  ∀ {machine steps cols}
    (stateCoverage : Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage : Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (left right : List (TransitionPredicateCode steps cols)) →
  interpretCodes stateCoverage symbolCoverage nonempty
    (appendCodes left right)
  ≡
  Transition.appendPredicates
    (interpretCodes stateCoverage symbolCoverage nonempty left)
    (interpretCodes stateCoverage symbolCoverage nonempty right)
interpretAppendCodes stateCoverage symbolCoverage nonempty [] right = refl
interpretAppendCodes stateCoverage symbolCoverage nonempty (x ∷ left) right
  rewrite interpretAppendCodes
    stateCoverage symbolCoverage nonempty left right = refl

codesForOneTimeExact :
  ∀ {machine steps cols timeIndex}
    (stateCoverage : Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage : Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (timeSlot : Global.Slot timeIndex steps)
    (starts : List (Transition.SomeWindowStart cols)) →
  interpretCodes stateCoverage symbolCoverage nonempty
    (codesForOneTime timeSlot starts)
  ≡
  Transition.predicatesForOneTime
    stateCoverage symbolCoverage nonempty timeSlot starts
codesForOneTimeExact stateCoverage symbolCoverage nonempty timeSlot [] = refl
codesForOneTimeExact stateCoverage symbolCoverage nonempty timeSlot
    (Transition.some-window-start columnIndex start ∷ rest)
  rewrite codesForOneTimeExact
    stateCoverage symbolCoverage nonempty timeSlot rest = refl

codesForAllTimesExact :
  ∀ {machine steps cols}
    (stateCoverage : Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage : Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (times : List (Transition.SomeSlot steps)) →
  interpretCodes stateCoverage symbolCoverage nonempty
    (codesForAllTimes {cols = cols} times)
  ≡
  Transition.predicatesForAllTimes
    stateCoverage symbolCoverage nonempty times
codesForAllTimesExact stateCoverage symbolCoverage nonempty [] = refl
codesForAllTimesExact {cols = cols}
    stateCoverage symbolCoverage nonempty
    (Transition.some-slot timeIndex timeSlot ∷ rest)
  rewrite interpretAppendCodes
      stateCoverage symbolCoverage nonempty
      (codesForOneTime timeSlot (Transition.allWindowStarts cols))
      (codesForAllTimes rest)
        | codesForOneTimeExact
            stateCoverage symbolCoverage nonempty
            timeSlot (Transition.allWindowStarts cols)
        | codesForAllTimesExact
            stateCoverage symbolCoverage nonempty rest =
  refl

allGlobalTransitionCodesExact :
  ∀ {machine}
    (stateCoverage : Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage : Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (steps cols : Nat) →
  interpretCodes stateCoverage symbolCoverage nonempty
    (allGlobalTransitionCodes steps cols)
  ≡
  Transition.allGlobalTransitionPredicates
    stateCoverage symbolCoverage nonempty steps cols
allGlobalTransitionCodesExact
    stateCoverage symbolCoverage nonempty steps cols =
  codesForAllTimesExact
    stateCoverage symbolCoverage nonempty
    (Transition.allSlots steps)

------------------------------------------------------------------------
-- CONSEQUENCE
--
-- The dynamic transition-predicate stream is now finite first-order syntax:
-- only time/window coordinates vary.  The remaining function-valued kernel is
-- ONE fixed `selectedRuleWindowPredicateWithCoverage` for the fixed machine,
-- plus the coordinate-index rename.  A standard-TM compiler therefore does not
-- need a general higher-order predicate interpreter.
------------------------------------------------------------------------
