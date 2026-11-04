module DASHI.Mathematics.Complexity.PNotEqualsNPBinaryCountdownExactRunExact where

------------------------------------------------------------------------
-- ARBITRARY-WORD EXACT STANDARD-TM RUN FOR THE XOR/RIPPLE COUNTDOWN
--
-- This closes the literal-machine gap left by the three-rule countdown fragment.
-- The fragment is first closed into the repository's actual
-- `CodedFiniteStandardTM` syntax, then decoded through the existing finite
-- presentation into the conventional split-tape machine.  No extensional next
-- oracle is introduced.
--
-- For every little-endian timer word:
--
--   * 0 bits propagate borrow: write 1 and move right;
--   * the first 1 resolves borrow: write 0 and stop in a fresh quiescent state;
--   * an all-zero word reaches the end marker and stops in the explicit
--     underflow state;
--   * the exact run index is the `countdownWork` already bounded by width+1.
--
-- Attribution remains local: the sibling IIT/XOR work motivated the microcode,
-- but this theorem is a DASHI complexity reconstruction over the literal coded
-- TM carrier.  No IIT quantity is used as complexity authority.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Maybe using (just; nothing)
import Data.Fin.Base as Fin

import DASHI.Mathematics.Complexity.CodedFiniteStandardMachineExact as Coded
import DASHI.Mathematics.Complexity.CodedFiniteStandardModeSumExact as Mode
import DASHI.Mathematics.Complexity.StandardFiniteTapePresentationExact as Presented
import DASHI.Mathematics.Complexity.StandardSingleTapeMachineExact as Standard
import DASHI.Mathematics.Complexity.ConcreteTapeStandardRunExact as Run
import DASHI.Mathematics.Complexity.PNotEqualsNPBinaryCountdownRuleFragmentExact as Fragment
import DASHI.Mathematics.Complexity.PNotEqualsNPBinaryCountdownCostExact as Cost

------------------------------------------------------------------------
-- 1. Close the already-owned three-rule fragment into literal coded syntax.
------------------------------------------------------------------------

countdownCode : Coded.CodedFiniteStandardTM
countdownCode =
  Mode.closeFragment
    Fragment.countdownFragment
    Fragment.endMarker
    Fragment.borrowControl
    Fragment.resolvedControl

countdownPresentation : Presented.FinitePresentedStandardTM
countdownPresentation = Coded.decodeCodedStandardTM countdownCode

countdownMachine :
  Standard.StandardSingleTapeMachine
    (Fin.Fin Fragment.stateCount)
    (Fin.Fin Fragment.symbolCount)
countdownMachine =
  Presented.finitePresentedStandardMachine countdownPresentation

------------------------------------------------------------------------
-- 2. Canonical timer tape representation.
------------------------------------------------------------------------

timerSymbol : Bool → Fin.Fin Fragment.symbolCount
timerSymbol false = Fragment.bit0
timerSymbol true = Fragment.bit1

-- Remaining cells to the right of the head, always terminated by the explicit
-- end marker.  Thus every nonterminal move-right step has a literal next cell.
timerRight : List Bool → List (Fin.Fin Fragment.symbolCount)
timerRight [] = Fragment.endMarker ∷ []
timerRight (bit ∷ rest) = timerSymbol bit ∷ timerRight rest

countdownStartFrom :
  List (Fin.Fin Fragment.symbolCount) →
  List Bool →
  Standard.StandardConfiguration countdownMachine
countdownStartFrom left [] =
  Standard.standard-configuration
    left Fragment.borrowControl Fragment.endMarker []
countdownStartFrom left (bit ∷ rest) =
  Standard.standard-configuration
    left Fragment.borrowControl (timerSymbol bit) (timerRight rest)

-- Endpoint produced by the literal rule fragment.  Bits already crossed while
-- borrow propagates are 0->1 and therefore accumulate on the left side as 1s.
countdownFinishFrom :
  List (Fin.Fin Fragment.symbolCount) →
  List Bool →
  Standard.StandardConfiguration countdownMachine
countdownFinishFrom left [] =
  Standard.standard-configuration
    left Fragment.underflowControl Fragment.endMarker []
countdownFinishFrom left (false ∷ rest) =
  countdownFinishFrom (Fragment.bit1 ∷ left) rest
countdownFinishFrom left (true ∷ rest) =
  Standard.standard-configuration
    left Fragment.resolvedControl Fragment.bit0 (timerRight rest)

countdownStart :
  List Bool → Standard.StandardConfiguration countdownMachine
countdownStart = countdownStartFrom []

countdownFinish :
  List Bool → Standard.StandardConfiguration countdownMachine
countdownFinish = countdownFinishFrom []

------------------------------------------------------------------------
-- 3. Literal one-step equations on the decoded finite rule table.
------------------------------------------------------------------------

countdownStepEnd :
  (left : List (Fin.Fin Fragment.symbolCount)) →
  Standard.standardNext countdownMachine (countdownStartFrom left [])
    ≡ just (countdownFinishFrom left [])
countdownStepEnd left = refl

countdownStepTrue :
  (left : List (Fin.Fin Fragment.symbolCount)) →
  (rest : List Bool) →
  Standard.standardNext
      countdownMachine
      (countdownStartFrom left (true ∷ rest))
    ≡ just (countdownFinishFrom left (true ∷ rest))
countdownStepTrue left rest = refl

countdownStepFalse :
  (left : List (Fin.Fin Fragment.symbolCount)) →
  (rest : List Bool) →
  Standard.standardNext
      countdownMachine
      (countdownStartFrom left (false ∷ rest))
    ≡ just (countdownStartFrom (Fragment.bit1 ∷ left) rest)
countdownStepFalse left [] = refl
countdownStepFalse left (next ∷ rest) = refl

------------------------------------------------------------------------
-- 4. Exact arbitrary-word run, indexed by the already-proved cost function.
------------------------------------------------------------------------

countdownExactRunFrom :
  (left : List (Fin.Fin Fragment.symbolCount)) →
  (bits : List Bool) →
  Run.StandardExactRun
    countdownMachine
    (Cost.countdownWork bits)
    (countdownStartFrom left bits)
    (countdownFinishFrom left bits)
countdownExactRunFrom left [] =
  Run.standardRunStep
    (countdownStepEnd left)
    Run.standardRunDone
countdownExactRunFrom left (false ∷ rest) =
  Run.standardRunStep
    (countdownStepFalse left rest)
    (countdownExactRunFrom (Fragment.bit1 ∷ left) rest)
countdownExactRunFrom left (true ∷ rest) =
  Run.standardRunStep
    (countdownStepTrue left rest)
    Run.standardRunDone

countdownExactRun :
  (bits : List Bool) →
  Run.StandardExactRun
    countdownMachine
    (Cost.countdownWork bits)
    (countdownStart bits)
    (countdownFinish bits)
countdownExactRun bits = countdownExactRunFrom [] bits

------------------------------------------------------------------------
-- 5. Every endpoint is actually quiescent under the same decoded rule table.
------------------------------------------------------------------------

countdownFinishQuiescentFrom :
  (left : List (Fin.Fin Fragment.symbolCount)) →
  (bits : List Bool) →
  Standard.standardNext countdownMachine (countdownFinishFrom left bits)
    ≡ nothing
countdownFinishQuiescentFrom left [] = refl
countdownFinishQuiescentFrom left (false ∷ rest) =
  countdownFinishQuiescentFrom (Fragment.bit1 ∷ left) rest
countdownFinishQuiescentFrom left (true ∷ rest) = refl

countdownFinishQuiescent :
  (bits : List Bool) →
  Standard.standardNext countdownMachine (countdownFinish bits) ≡ nothing
countdownFinishQuiescent bits =
  countdownFinishQuiescentFrom [] bits

------------------------------------------------------------------------
-- 6. Max-cut boundary.
------------------------------------------------------------------------

record BinaryCountdownExactRunBoundary : Set where
  constructor binary-countdown-exact-run-boundary
  field
    literalCodedMachinePaid : Bool
    decodedStandardMachinePaid : Bool
    arbitraryWordExactRunPaid : Bool
    exactRunUsesWidthBoundedCost : Bool
    resolvedAndUnderflowEndpointsQuiescent : Bool
    separateTimerCandidateHeadTravelStillRequired : Bool
    repeatedCountdownResetStillRequired : Bool
    finalSameCookBudgetClosureStillRequired : Bool
    iitPhiIsComplexityLowerBound : Bool

open BinaryCountdownExactRunBoundary public

canonicalBinaryCountdownExactRunBoundary : BinaryCountdownExactRunBoundary
canonicalBinaryCountdownExactRunBoundary =
  binary-countdown-exact-run-boundary
    true true true true true
    true true true false

literalCountdownRunDoesNotCloseResourceFixedPoint :
  finalSameCookBudgetClosureStillRequired
    canonicalBinaryCountdownExactRunBoundary ≡ true
literalCountdownRunDoesNotCloseResourceFixedPoint = refl
