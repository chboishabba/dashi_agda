module DASHI.Mathematics.Complexity.StandardFiniteTapePresentationExact where

------------------------------------------------------------------------
-- FINITE PRESENTATION OF THE CONVENTIONAL SINGLE-TAPE TM
--
-- A complexity model needs finite syntax, not merely an extensional
-- transition function.  This owner records exactly the finite control data:
-- finite state/symbol enumerations, blank/initial/accepting symbols/states,
-- and a literal deterministic rule list.
--
-- The conventional split-tape transition function is DERIVED from this finite
-- program text by the existing sequential first-match interpreter.  Thus no
-- separate extensional transition oracle is stored, and conversion to the
-- existing ConcreteTapeMachine carrier is data-preserving by construction.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.PNotEqualsNPConcreteTapeRuleKeyDeterminismExact as Determinism
import DASHI.Mathematics.Complexity.StandardSingleTapeMachineExact as Standard

------------------------------------------------------------------------
-- Finite, rule-table presented conventional TM syntax.
------------------------------------------------------------------------

record FinitePresentedStandardTM : Set₁ where
  field
    State : Set
    Symbol : Set
    finiteState : Local.FiniteEnumeration State
    finiteSymbol : Local.FiniteEnumeration Symbol
    blank : Symbol
    initialState : State
    acceptingState : State
    rules : List (Local.TapeRule State Symbol)

    -- Bare rule lists are not deterministic in the repository carrier; the
    -- standard finite presentation records the actual dispatch uniqueness law.
    dispatchUnique :
      ∀ {left right : Local.TapeRule State Symbol} →
      Local.RuleOccurs left rules →
      Local.RuleOccurs right rules →
      Local.sourceState left ≡ Local.sourceState right →
      Local.readSymbol left ≡ Local.readSymbol right →
      left ≡ right

open FinitePresentedStandardTM public

------------------------------------------------------------------------
-- Exact concrete view and derived conventional machine.
------------------------------------------------------------------------

finitePresentedStandardToConcrete :
  FinitePresentedStandardTM → Local.ConcreteTapeMachine
finitePresentedStandardToConcrete presentation = record
  { Local.State = State presentation
  ; Local.Symbol = Symbol presentation
  ; Local.finiteState = finiteState presentation
  ; Local.finiteSymbol = finiteSymbol presentation
  ; Local.blank = blank presentation
  ; Local.initialState = initialState presentation
  ; Local.acceptingState = acceptingState presentation
  ; Local.rules = rules presentation
  }

finitePresentedStandardMachine :
  (presentation : FinitePresentedStandardTM) →
  Standard.StandardSingleTapeMachine
    (State presentation)
    (Symbol presentation)
finitePresentedStandardMachine presentation =
  Standard.standardControlOfConcrete
    (finitePresentedStandardToConcrete presentation)

finitePresentedStandardToConcrete_dispatchUnique :
  (presentation : FinitePresentedStandardTM) →
  Determinism.RuleKeyDeterministic
    (finitePresentedStandardToConcrete presentation)
finitePresentedStandardToConcrete_dispatchUnique presentation =
  dispatchUnique presentation

@[simp] finitePresentedStandard_blank :
  (presentation : FinitePresentedStandardTM) →
  Standard.blank (finitePresentedStandardMachine presentation)
    ≡ blank presentation
finitePresentedStandard_blank presentation = refl

@[simp] finitePresentedStandard_initialState :
  (presentation : FinitePresentedStandardTM) →
  Standard.initialState (finitePresentedStandardMachine presentation)
    ≡ initialState presentation
finitePresentedStandard_initialState presentation = refl

@[simp] finitePresentedStandard_acceptingState :
  (presentation : FinitePresentedStandardTM) →
  Standard.acceptingState (finitePresentedStandardMachine presentation)
    ≡ acceptingState presentation
finitePresentedStandard_acceptingState presentation = refl

------------------------------------------------------------------------
-- Deterministic ConcreteTapeMachine -> finite standard syntax is canonical.
------------------------------------------------------------------------

concreteToFinitePresentedStandard :
  (concrete : Local.ConcreteTapeMachine) →
  Determinism.RuleKeyDeterministic concrete →
  FinitePresentedStandardTM
concreteToFinitePresentedStandard concrete deterministic = record
  { State = Local.State concrete
  ; Symbol = Local.Symbol concrete
  ; finiteState = Local.finiteState concrete
  ; finiteSymbol = Local.finiteSymbol concrete
  ; blank = Local.blank concrete
  ; initialState = Local.initialState concrete
  ; acceptingState = Local.acceptingState concrete
  ; rules = Local.rules concrete
  ; dispatchUnique = deterministic
  }

------------------------------------------------------------------------
-- Round-trip data are literally the same concrete finite program.
------------------------------------------------------------------------

concreteRoundTrip :
  (concrete : Local.ConcreteTapeMachine) →
  (deterministic : Determinism.RuleKeyDeterministic concrete) →
  finitePresentedStandardToConcrete
    (concreteToFinitePresentedStandard concrete deterministic)
  ≡ concrete
concreteRoundTrip concrete deterministic = refl

/-- The conventional machine obtained after the round trip is therefore
exactly the repository's canonical standard control adapter for the original
concrete machine. -/
concreteStandardMachineRoundTrip :
  (concrete : Local.ConcreteTapeMachine) →
  (deterministic : Determinism.RuleKeyDeterministic concrete) →
  finitePresentedStandardMachine
      (concreteToFinitePresentedStandard concrete deterministic)
    ≡ Standard.standardControlOfConcrete concrete
concreteStandardMachineRoundTrip concrete deterministic = refl

------------------------------------------------------------------------
-- MAX-CUT STATUS
--
-- PAID (subject to exact-head Agda certification):
-- * conventional deterministic single-tape machines now have finite program
--   syntax suitable for a complexity-model equivalence theorem;
-- * no transition oracle is hidden: the transition is derived by the existing
--   literal first-match rule-table interpreter;
-- * finite standard syntax -> ConcreteTapeMachine preserves all finite data;
-- * deterministic ConcreteTapeMachine -> finite standard syntax is canonical
--   and round-trips definitionally;
-- * the derived conventional machine also round-trips definitionally.
--
-- REMAINING MODEL-INVARIANCE WORK:
-- * chained tape/configuration run transport (the one-step local weld is
--   already in ConcreteTapeStandardOneStepExact);
-- * polynomial clock accounting using fixed |rules| control overhead and the
--   existing linear T-step blank padding;
-- * language/acceptance preservation.
--
-- After those run-level statements, freeze the P representation substrate.
------------------------------------------------------------------------
