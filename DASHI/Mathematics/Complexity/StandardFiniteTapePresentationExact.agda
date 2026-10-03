module DASHI.Mathematics.Complexity.StandardFiniteTapePresentationExact where

------------------------------------------------------------------------
-- FINITE PRESENTATION OF THE CONVENTIONAL SINGLE-TAPE TM
--
-- A complexity model needs finite syntax, not merely an extensional
-- transition function.  This owner equips the conventional split-tape machine
-- with the exact finite data already used by ConcreteTapeMachine:
-- finite state/symbol enumerations and a literal rule list.  The standard
-- transition function is required to be exactly the sequential first-match
-- interpretation of that list.
--
-- Consequently conversion to ConcreteTapeMachine is data-preserving, and the
-- Concrete -> standard control adapter recovers the original transition
-- function extensionally.  No hidden oracle transition survives the bridge.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Maybe using (Maybe)
open import Relation.Binary.PropositionalEquality using (cong)

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.PNotEqualsNPConcreteTapeRuleTableInterpreterExact as Interpreter
import DASHI.Mathematics.Complexity.PNotEqualsNPConcreteTapeRuleKeyDeterminismExact as Determinism
import DASHI.Mathematics.Complexity.StandardSingleTapeMachineExact as Standard

------------------------------------------------------------------------
-- Finite, rule-table presented conventional TM.
------------------------------------------------------------------------

record FinitePresentedStandardTM : Set₁ where
  field
    State : Set
    Symbol : Set
    finiteState : Local.FiniteEnumeration State
    finiteSymbol : Local.FiniteEnumeration Symbol
    machine : Standard.StandardSingleTapeMachine State Symbol
    rules : List (Local.TapeRule State Symbol)

    -- Bare rule lists are not deterministic in the existing carrier; the
    -- standard presentation explicitly records the required uniqueness law.
    dispatchUnique :
      ∀ {left right : Local.TapeRule State Symbol} →
      Local.RuleOccurs left rules →
      Local.RuleOccurs right rules →
      Local.sourceState left ≡ Local.sourceState right →
      Local.readSymbol left ≡ Local.readSymbol right →
      left ≡ right

    -- The extensional transition function contains no more information than
    -- the literal finite program text: it is exactly first-match execution of
    -- this rule list with the supplied equality deciders.
    transitionIsFirstMatch :
      (q : State) →
      (a : Symbol) →
      Standard.transition machine q a
      ≡ presentedTransition q a

  presentedConcreteView : Local.ConcreteTapeMachine
  presentedConcreteView = record
    { Local.State = State
    ; Local.Symbol = Symbol
    ; Local.finiteState = finiteState
    ; Local.finiteSymbol = finiteSymbol
    ; Local.blank = Standard.blank machine
    ; Local.initialState = Standard.initialState machine
    ; Local.acceptingState = Standard.acceptingState machine
    ; Local.rules = rules
    }

  presentedTransition :
    State → Symbol → Maybe (Standard.StandardTransition State Symbol)
  presentedTransition q a =
    Standard.concreteControlTransition presentedConcreteView q a

open FinitePresentedStandardTM public

------------------------------------------------------------------------
-- Literal conversion to the existing ConcreteTapeMachine carrier.
------------------------------------------------------------------------

finitePresentedStandardToConcrete :
  FinitePresentedStandardTM → Local.ConcreteTapeMachine
finitePresentedStandardToConcrete presentation =
  presentedConcreteView presentation

finitePresentedStandardToConcrete_dispatchUnique :
  (presentation : FinitePresentedStandardTM) →
  Determinism.RuleKeyDeterministic
    (finitePresentedStandardToConcrete presentation)
finitePresentedStandardToConcrete_dispatchUnique presentation =
  dispatchUnique presentation

------------------------------------------------------------------------
-- Concrete -> finite-presented-standard is canonical.
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
  ; machine = Standard.standardControlOfConcrete concrete
  ; rules = Local.rules concrete
  ; dispatchUnique = deterministic
  ; transitionIsFirstMatch = λ q a → refl
  }

------------------------------------------------------------------------
-- Round-trip data are literally the same concrete program.
------------------------------------------------------------------------

concreteRoundTrip :
  (concrete : Local.ConcreteTapeMachine) →
  (deterministic : Determinism.RuleKeyDeterministic concrete) →
  finitePresentedStandardToConcrete
    (concreteToFinitePresentedStandard concrete deterministic)
  ≡ concrete
concreteRoundTrip concrete deterministic = refl

/-- Going standard presentation -> concrete -> standard recovers the original
transition function pointwise. -/
finitePresentedStandardTransition_roundTrip :
  (presentation : FinitePresentedStandardTM) →
  (q : State presentation) →
  (a : Symbol presentation) →
  Standard.transition
      (Standard.standardControlOfConcrete
        (finitePresentedStandardToConcrete presentation)) q a
    ≡ Standard.transition (machine presentation) q a
finitePresentedStandardTransition_roundTrip presentation q a =
  (transitionIsFirstMatch presentation q a)⁻¹
  where
    _⁻¹ : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
    refl ⁻¹ = refl

------------------------------------------------------------------------
-- MAX-CUT STATUS
--
-- PAID (subject to exact-head Agda certification):
-- * a conventional standard single-tape machine now has a finite program
--   presentation suitable for complexity theory;
-- * no transition oracle is hidden: transition = sequential rule-table scan;
-- * standard presentation -> ConcreteTapeMachine preserves all program data;
-- * deterministic ConcreteTapeMachine -> finite standard presentation is
--   canonical and round-trips definitionally;
-- * standard transition is recovered pointwise after the round trip.
--
-- REMAINING MODEL-INVARIANCE WORK:
-- * tape/configuration encoding and chained run transport (one-step local
--   correspondence already exists in ConcreteTapeStandardOneStepExact);
-- * polynomial clock accounting, using static |rules| control overhead and
--   existing linear T-step blank padding;
-- * language/acceptance preservation.
--
-- After those run-level statements, freeze the P representation substrate.
------------------------------------------------------------------------
