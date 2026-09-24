module DASHI.Mathematics.Complexity.PNotEqualsNPConcreteTapeDeterminismNoGoExact where

------------------------------------------------------------------------
-- BARE CONCRETE TAPE PROGRAMS NEED NOT BE DETERMINISTIC
--
-- The finite serializer works on ConcreteTapeMachine, but that carrier stores
-- only a literal rule list.  It does not require uniqueness of a rule for a
-- given (sourceState, readSymbol) pair.
--
-- This owner gives a concrete finite machine with TWO conflicting rules for the
-- same source/read pair and proves both rules occur in the machine.
--
-- Therefore no generic adapter
--
--   ConcreteTapeMachine -> DeterministicMachine
--
-- can derive a canonical deterministic next-step function from the bare rule
-- list without an extra determinism/selection premise.
--
-- This explains the currently unpaid genericMachineAdapter boundary and keeps
-- the finite-program-code layer honest.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local

------------------------------------------------------------------------
-- Exact Bool equality.
------------------------------------------------------------------------

boolEqual : Bool → Bool → Bool
boolEqual false false = true
boolEqual false true = false
boolEqual true false = false
boolEqual true true = true

boolEqualRefl :
  (value : Bool) →
  boolEqual value value ≡ true
boolEqualRefl false = refl
boolEqualRefl true = refl

boolEqualSound :
  ∀ {left right : Bool} →
  boolEqual left right ≡ true →
  left ≡ right
boolEqualSound {false} {false} proof = refl
boolEqualSound {false} {true} ()
boolEqualSound {true} {false} ()
boolEqualSound {true} {true} proof = refl

boolEnumeration :
  Local.FiniteEnumeration Bool
boolEnumeration = record
  { Local.values =
      false ∷ true ∷ []
  ; Local.occurs =
      λ value → ⊤
  ; Local.complete =
      λ value → tt
  ; Local.decideEqual =
      boolEqual
  ; Local.decideEqualRefl =
      boolEqualRefl
  ; Local.decideEqualSound =
      boolEqualSound
  }

------------------------------------------------------------------------
-- Two conflicting rules for the same source/read pair.
------------------------------------------------------------------------

firstRule :
  Local.TapeRule Bool Bool
firstRule =
  Local.tape-rule
    false
    false
    false
    false
    Local.stayPut

secondRule :
  Local.TapeRule Bool Bool
secondRule =
  Local.tape-rule
    false
    false
    true
    false
    Local.stayPut

conflictingMachine :
  Local.ConcreteTapeMachine
conflictingMachine = record
  { Local.State =
      Bool
  ; Local.Symbol =
      Bool
  ; Local.finiteState =
      boolEnumeration
  ; Local.finiteSymbol =
      boolEnumeration
  ; Local.blank =
      false
  ; Local.initialState =
      false
  ; Local.acceptingState =
      true
  ; Local.rules =
      firstRule ∷ secondRule ∷ []
  }

firstRuleOccurs :
  Local.RuleOccurs
    firstRule
    (Local.rules conflictingMachine)
firstRuleOccurs =
  Local.ruleHere

secondRuleOccurs :
  Local.RuleOccurs
    secondRule
    (Local.rules conflictingMachine)
secondRuleOccurs =
  Local.ruleThere
    Local.ruleHere

------------------------------------------------------------------------
-- They have the same dispatch key but genuinely different next control states.
------------------------------------------------------------------------

sameSourceState :
  Local.sourceState firstRule
  ≡ Local.sourceState secondRule
sameSourceState =
  refl

sameReadSymbol :
  Local.readSymbol firstRule
  ≡ Local.readSymbol secondRule
sameReadSymbol =
  refl

differentTargetState :
  Local.targetState firstRule
  ≡ Local.targetState secondRule →
  ⊥
differentTargetState ()

------------------------------------------------------------------------
-- A uniqueness law for dispatch keys fails on the bare carrier.
------------------------------------------------------------------------

RuleDispatchUnique :
  Local.ConcreteTapeMachine →
  Set
RuleDispatchUnique machine =
  ∀ {left right :
      Local.TapeRule
        (Local.State machine)
        (Local.Symbol machine)} →
  Local.RuleOccurs left (Local.rules machine) →
  Local.RuleOccurs right (Local.rules machine) →
  Local.sourceState left ≡ Local.sourceState right →
  Local.readSymbol left ≡ Local.readSymbol right →
  left ≡ right

conflictingMachineIsNotDispatchUnique :
  RuleDispatchUnique conflictingMachine →
  ⊥
conflictingMachineIsNotDispatchUnique unique =
  differentTargetState
    (congruenceTarget
      (unique
        firstRuleOccurs
        secondRuleOccurs
        sameSourceState
        sameReadSymbol))
  where
    congruenceTarget :
      firstRule ≡ secondRule →
      Local.targetState firstRule
      ≡ Local.targetState secondRule
    congruenceTarget refl =
      refl

------------------------------------------------------------------------
-- Research consequence.
--
-- The existing finite static code is a genuine syntax object, but an
-- executable deterministic realization needs EXTRA structure, at minimum:
--
--   * dispatch uniqueness / deterministic rule selection;
--   * total step semantics on represented configurations;
--   * input encoding for Cook formulas;
--   * output/acceptance equality with the polynomial SAT candidate.
--
-- Those premises cannot be recovered from ConcreteTapeMachine alone.
------------------------------------------------------------------------
