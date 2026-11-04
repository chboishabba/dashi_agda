module DASHI.Mathematics.Complexity.PNotEqualsNPBinaryCountdownRuleFragmentExact where

------------------------------------------------------------------------
-- LITERAL FINITE RULE-TABLE FRAGMENT FOR ONE RIPPLE-BORROW DECREMENT PASS
--
-- Tape convention for the timer word:
--   * symbols are little-endian bit0 / bit1 followed by endMarker;
--   * control starts in borrowControl, representing incoming borrow=true;
--   * read 0: write 1, keep borrow, move right;
--   * read 1: write 0, resolve borrow and enter quiescent resolvedControl;
--   * read end: preserve end marker and enter quiescent underflowControl.
--
-- This is the finite standard-machine rule-table realization of the local
-- XOR/borrow countdown cell exposed by PNotEqualsNPXORCountdownMicrocodeExact.
-- It pays literal finite control and quiescent timer endpoints.  The remaining
-- timer theorem is the arbitrary-word exact-run correspondence plus its exact
-- step/cost bound and integration with the enclosing candidate phase.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)
import Data.Fin.Base as Fin

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.CodedFiniteStandardModeSumExact as Mode

------------------------------------------------------------------------
-- 1. Literal finite states and alphabet.
------------------------------------------------------------------------

stateCount : Nat
stateCount = 3

symbolCount : Nat
symbolCount = 3

borrowControl : Fin.Fin stateCount
borrowControl = Fin.zero

resolvedControl : Fin.Fin stateCount
resolvedControl = Fin.suc Fin.zero

underflowControl : Fin.Fin stateCount
underflowControl = Fin.suc (Fin.suc Fin.zero)

bit0 : Fin.Fin symbolCount
bit0 = Fin.zero

bit1 : Fin.Fin symbolCount
bit1 = Fin.suc Fin.zero

endMarker : Fin.Fin symbolCount
endMarker = Fin.suc (Fin.suc Fin.zero)

------------------------------------------------------------------------
-- 2. Three literal rules implement one ripple-borrow pass.
------------------------------------------------------------------------

borrowOnZeroRule :
  Local.TapeRule (Fin.Fin stateCount) (Fin.Fin symbolCount)
borrowOnZeroRule =
  Local.tape-rule
    borrowControl bit0
    borrowControl bit1
    Local.moveRight

resolveOnOneRule :
  Local.TapeRule (Fin.Fin stateCount) (Fin.Fin symbolCount)
resolveOnOneRule =
  Local.tape-rule
    borrowControl bit1
    resolvedControl bit0
    Local.stayPut

underflowOnEndRule :
  Local.TapeRule (Fin.Fin stateCount) (Fin.Fin symbolCount)
underflowOnEndRule =
  Local.tape-rule
    borrowControl endMarker
    underflowControl endMarker
    Local.stayPut

countdownRules :
  List (Local.TapeRule (Fin.Fin stateCount) (Fin.Fin symbolCount))
countdownRules =
  borrowOnZeroRule ∷ resolveOnOneRule ∷ underflowOnEndRule ∷ []

------------------------------------------------------------------------
-- 3. Literal dispatch uniqueness.
------------------------------------------------------------------------

countdownDispatchUnique :
  ∀ {left right} →
  Local.RuleOccurs left countdownRules →
  Local.RuleOccurs right countdownRules →
  Local.sourceState left ≡ Local.sourceState right →
  Local.readSymbol left ≡ Local.readSymbol right →
  left ≡ right
countdownDispatchUnique Local.ruleHere Local.ruleHere sourceEq readEq = refl
countdownDispatchUnique Local.ruleHere (Local.ruleThere Local.ruleHere) sourceEq ()
countdownDispatchUnique Local.ruleHere (Local.ruleThere (Local.ruleThere Local.ruleHere)) sourceEq ()
countdownDispatchUnique Local.ruleHere (Local.ruleThere (Local.ruleThere (Local.ruleThere ()))) sourceEq readEq
countdownDispatchUnique (Local.ruleThere Local.ruleHere) Local.ruleHere sourceEq ()
countdownDispatchUnique (Local.ruleThere Local.ruleHere) (Local.ruleThere Local.ruleHere) sourceEq readEq = refl
countdownDispatchUnique (Local.ruleThere Local.ruleHere) (Local.ruleThere (Local.ruleThere Local.ruleHere)) sourceEq ()
countdownDispatchUnique (Local.ruleThere Local.ruleHere) (Local.ruleThere (Local.ruleThere (Local.ruleThere ()))) sourceEq readEq
countdownDispatchUnique (Local.ruleThere (Local.ruleThere Local.ruleHere)) Local.ruleHere sourceEq ()
countdownDispatchUnique (Local.ruleThere (Local.ruleThere Local.ruleHere)) (Local.ruleThere Local.ruleHere) sourceEq ()
countdownDispatchUnique (Local.ruleThere (Local.ruleThere Local.ruleHere)) (Local.ruleThere (Local.ruleThere Local.ruleHere)) sourceEq readEq = refl
countdownDispatchUnique (Local.ruleThere (Local.ruleThere Local.ruleHere)) (Local.ruleThere (Local.ruleThere (Local.ruleThere ()))) sourceEq readEq
countdownDispatchUnique (Local.ruleThere (Local.ruleThere (Local.ruleThere ()))) rightOccurs sourceEq readEq

countdownFragment : Mode.CodedModeFragment symbolCount
countdownFragment = record
  { Mode.stateCount = stateCount
  ; Mode.rules = countdownRules
  ; Mode.dispatchUnique = countdownDispatchUnique
  }

------------------------------------------------------------------------
-- 4. The two terminal timer controls are genuinely quiescent in this fragment.
------------------------------------------------------------------------

resolvedControlHasNoResidentRule :
  ∀ {rule} →
  Local.RuleOccurs rule countdownRules →
  Local.sourceState rule ≡ resolvedControl →
  ⊥
resolvedControlHasNoResidentRule Local.ruleHere ()
resolvedControlHasNoResidentRule (Local.ruleThere Local.ruleHere) ()
resolvedControlHasNoResidentRule (Local.ruleThere (Local.ruleThere Local.ruleHere)) ()
resolvedControlHasNoResidentRule (Local.ruleThere (Local.ruleThere (Local.ruleThere ()))) sourceEq

underflowControlHasNoResidentRule :
  ∀ {rule} →
  Local.RuleOccurs rule countdownRules →
  Local.sourceState rule ≡ underflowControl →
  ⊥
underflowControlHasNoResidentRule Local.ruleHere ()
underflowControlHasNoResidentRule (Local.ruleThere Local.ruleHere) ()
underflowControlHasNoResidentRule (Local.ruleThere (Local.ruleThere Local.ruleHere)) ()
underflowControlHasNoResidentRule (Local.ruleThere (Local.ruleThere (Local.ruleThere ()))) sourceEq

------------------------------------------------------------------------
-- 5. Source-level receipt.
------------------------------------------------------------------------

record BinaryCountdownRuleFragmentBoundary : Set where
  constructor binary-countdown-rule-fragment-boundary
  field
    literalFiniteRuleTablePaid : Bool
    bitZeroBorrowPropagationPaid : Bool
    bitOneBorrowResolutionPaid : Bool
    explicitUnderflowEndpointPaid : Bool
    resolvedEndpointQuiescentPaid : Bool
    underflowEndpointQuiescentPaid : Bool
    arbitraryWordRunCorrespondenceStillRequired : Bool
    exactTimerCostStillRequired : Bool

canonicalBinaryCountdownRuleFragmentBoundary :
  BinaryCountdownRuleFragmentBoundary
canonicalBinaryCountdownRuleFragmentBoundary =
  binary-countdown-rule-fragment-boundary
    true true true true true true true true
