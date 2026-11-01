module DASHI.Mathematics.Complexity.StandardSingleTapeMachineExact where

------------------------------------------------------------------------
-- CONVENTIONAL DETERMINISTIC SINGLE-TAPE TURING MACHINE
--
-- The older generic `DeterministicMachine` intentionally permits an arbitrary
-- configuration type and arbitrary partial next function.  It is therefore
-- too extensional to serve as the standard-machine side of a model-invariance
-- theorem.
--
-- This owner introduces only the conventional operational carrier needed for
-- that theorem:
--
--   * finite-control state type and tape-symbol type;
--   * blank, initial and accepting states;
--   * partial transition function (q,a) |-> (q',b,d);
--   * split-tape configurations, with the cells nearest the head first on
--     both left and right lists;
--   * literal one-step execution with blank extension at either end.
--
-- It then derives the transition function of an existing ConcreteTapeMachine
-- from the repository's literal sequential first-match rule lookup.  Thus the
-- standard control semantics and concrete rule-table semantics are already the
-- same object in the Concrete -> standard direction.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Maybe using (Maybe; nothing; just)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat.Base using (_≤_)
open import Data.Product using (_×_; _,_; ∃)

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeCanonicalCellBitsExact as Canonical
import DASHI.Mathematics.Complexity.PNotEqualsNPConcreteTapeRuleTableInterpreterExact as Interpreter
import DASHI.Mathematics.Complexity.PNotEqualsNPConcreteTapeRuleKeyDeterminismExact as Determinism

------------------------------------------------------------------------
-- Conventional transition and machine carriers.
------------------------------------------------------------------------

record StandardTransition
    (State Symbol : Set) : Set where
  constructor standard-transition
  field
    targetState : State
    writeSymbol : Symbol
    direction : Local.Direction

open StandardTransition public

record StandardSingleTapeMachine
    (State Symbol : Set) : Set where
  field
    blank : Symbol
    initialState : State
    acceptingState : State
    transition : State → Symbol → Maybe (StandardTransition State Symbol)

open StandardSingleTapeMachine public

record StandardConfiguration
    {State Symbol : Set}
    (machine : StandardSingleTapeMachine State Symbol) : Set where
  constructor standard-configuration
  field
    -- Nearest tape cell first.  An empty side denotes an all-blank tail.
    left : List Symbol
    state : State
    scanned : Symbol
    right : List Symbol

open StandardConfiguration public

------------------------------------------------------------------------
-- Literal standard one-step semantics.
------------------------------------------------------------------------

standardApplyTransition :
  ∀ {State Symbol}
    (machine : StandardSingleTapeMachine State Symbol) →
  StandardConfiguration machine →
  StandardTransition State Symbol →
  StandardConfiguration machine
standardApplyTransition machine
    (standard-configuration [] q a right)
    (standard-transition q' b Local.moveLeft) =
  standard-configuration [] q' (blank machine) (b ∷ right)
standardApplyTransition machine
    (standard-configuration (l ∷ left) q a right)
    (standard-transition q' b Local.moveLeft) =
  standard-configuration left q' l (b ∷ right)
standardApplyTransition machine
    (standard-configuration left q a right)
    (standard-transition q' b Local.stayPut) =
  standard-configuration left q' b right
standardApplyTransition machine
    (standard-configuration left q a [])
    (standard-transition q' b Local.moveRight) =
  standard-configuration (b ∷ left) q' (blank machine) []
standardApplyTransition machine
    (standard-configuration left q a (r ∷ right))
    (standard-transition q' b Local.moveRight) =
  standard-configuration (b ∷ left) q' r right

standardNext :
  ∀ {State Symbol}
    (machine : StandardSingleTapeMachine State Symbol) →
  StandardConfiguration machine →
  Maybe (StandardConfiguration machine)
standardNext machine configuration
    with transition machine (state configuration) (scanned configuration)
... | nothing = nothing
... | just selected =
  just (standardApplyTransition machine configuration selected)

standardAccepting :
  ∀ {State Symbol}
    {machine : StandardSingleTapeMachine State Symbol} →
  StandardConfiguration machine → Set
standardAccepting {machine = machine} configuration =
  state configuration ≡ acceptingState machine

------------------------------------------------------------------------
-- Same-object control adapter from ConcreteTapeMachine.
------------------------------------------------------------------------

matchedRuleTransition :
  ∀ {machine q a rules} →
  Interpreter.MatchedRule machine q a rules →
  StandardTransition (Local.State machine) (Local.Symbol machine)
matchedRuleTransition matched =
  standard-transition
    (Local.targetState (Interpreter.rule matched))
    (Local.writeSymbol (Interpreter.rule matched))
    (Local.direction (Interpreter.rule matched))

concreteControlTransition :
  (machine : Local.ConcreteTapeMachine) →
  Local.State machine →
  Local.Symbol machine →
  Maybe (StandardTransition (Local.State machine) (Local.Symbol machine))
concreteControlTransition machine q a
    with Interpreter.fetchConcreteRule machine q a
... | nothing = nothing
... | just matched = just (matchedRuleTransition matched)

standardControlOfConcrete :
  (machine : Local.ConcreteTapeMachine) →
  StandardSingleTapeMachine
    (Local.State machine)
    (Local.Symbol machine)
standardControlOfConcrete machine = record
  { blank = Local.blank machine
  ; initialState = Local.initialState machine
  ; acceptingState = Local.acceptingState machine
  ; transition = concreteControlTransition machine
  }

------------------------------------------------------------------------
-- The adapter uses exactly the existing first-match result.
------------------------------------------------------------------------

concreteControlTransition_of_fetch :
  ∀ {machine q a matched} →
  Interpreter.fetchConcreteRule machine q a ≡ just matched →
  concreteControlTransition machine q a
    ≡ just (matchedRuleTransition matched)
concreteControlTransition_of_fetch {machine} {q} {a} {matched} fetchEq
    rewrite fetchEq = refl

concreteControlTransition_nothing :
  ∀ {machine q a} →
  Interpreter.fetchConcreteRule machine q a ≡ nothing →
  concreteControlTransition machine q a ≡ nothing
concreteControlTransition_nothing {machine} {q} {a} fetchEq
    rewrite fetchEq = refl

------------------------------------------------------------------------
-- Under the already-existing dispatch-uniqueness condition, every listed
-- relational rule with key (q,a) is exactly the standard transition selected
-- by the adapter.
------------------------------------------------------------------------

listedRuleDeterminesStandardTransition :
  ∀ {machine q a wanted}
    (deterministic : Determinism.RuleKeyDeterministic machine) →
  Local.RuleOccurs wanted (Local.rules machine) →
  Local.sourceState wanted ≡ q →
  Local.readSymbol wanted ≡ a →
  ∃ λ matched →
    Interpreter.fetchConcreteRule machine q a ≡ just matched
    × concreteControlTransition machine q a
        ≡ just (standard-transition
          (Local.targetState wanted)
          (Local.writeSymbol wanted)
          (Local.direction wanted))
listedRuleDeterminesStandardTransition
    {machine} {q} {a} {wanted}
    deterministic occurs sourceEq readEq
    with Determinism.fetchConcreteRuleCompleteUnique
      deterministic occurs sourceEq readEq
... | matched , fetchEq , ruleEq
    rewrite fetchEq | ruleEq =
  matched , refl , refl

------------------------------------------------------------------------
-- Control-fetch cost is the literal concrete rule-table scan cost, hence a
-- fixed machine contributes at most its static table width per standard step.
------------------------------------------------------------------------

standardControlFetchWork :
  (machine : Local.ConcreteTapeMachine) →
  Local.State machine →
  Local.Symbol machine → Nat
standardControlFetchWork = Interpreter.fetchConcreteRuleWork

standardControlFetchWorkBound :
  (machine : Local.ConcreteTapeMachine) →
  (q : Local.State machine) →
  (a : Local.Symbol machine) →
  standardControlFetchWork machine q a
    ≤ Canonical.listLength (Local.rules machine)
standardControlFetchWorkBound = Interpreter.fetchConcreteRuleWorkBound

------------------------------------------------------------------------
-- MAX-CUT STATUS
--
-- PAID (subject to exact-head Agda certification):
-- * conventional deterministic split-tape TM carrier and executable step;
-- * exact ConcreteTapeMachine -> standard transition function using the
--   existing literal sequential first-match lookup;
-- * under RuleDispatchUnique, every relational listed rule induces exactly
--   that standard transition;
-- * one control lookup costs at most the static rule-table width.
--
-- NEXT MODEL-INVARIANCE BRIDGE:
-- * project an intrinsic concrete row to a split-tape configuration and prove
--   one-step equality with `standardNext`;
-- * use existing T+1 blank-margin padding to iterate this for T steps;
-- * provide the reverse finite rule-table presentation for conventional
--   standard machines and prove polynomial clock transport;
-- * then freeze representation infrastructure.
------------------------------------------------------------------------
