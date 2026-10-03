module DASHI.Mathematics.Complexity.ConcreteTapeStandardLanguageEquivalenceExact where

------------------------------------------------------------------------
-- EXACT GUARDED-INPUT ACCEPTANCE IFF
--
-- This is the language-level wrapper over the two already-owned run maps:
--
--   concrete accepting run -> standard run   (StandardRunExact)
--   standard run -> concrete run             (StandardReverseRunExact)
--
-- Both sides start from the canonical projection of the SAME guarded literal
-- input row and use the SAME exact step budget. No alternate language,
-- interpreter, or machine semantics are introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Product using (_×_; _,_)

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeWellFormedConfigurationExact as WF
import DASHI.Mathematics.Complexity.ConcreteTapeLocalityCharacterizationExact as Character
import DASHI.Mathematics.Complexity.ConcreteTapeInputInitialRowExact as Input
import DASHI.Mathematics.Complexity.ConcreteTapeTimeBudgetPaddingExact as Guard
import DASHI.Mathematics.Complexity.ConcreteTapeRunCNFWeldExact as Run
import DASHI.Mathematics.Complexity.ConcreteTapeAcceptingRunCNFExact as Accepting
import DASHI.Mathematics.Complexity.PNotEqualsNPConcreteTapeRuleKeyDeterminismExact as Determinism
import DASHI.Mathematics.Complexity.StandardSingleTapeMachineExact as Standard
import DASHI.Mathematics.Complexity.ConcreteTapeStandardCanonicalProjectionExact as Canonical
import DASHI.Mathematics.Complexity.ConcreteTapeStandardRunExact as Forward
import DASHI.Mathematics.Complexity.ConcreteTapeStandardReverseRunExact as Reverse
import DASHI.Mathematics.Complexity.StandardFiniteTapePresentationExact as Presented

------------------------------------------------------------------------
-- The canonical guarded start configuration.
------------------------------------------------------------------------

guardedInitialUnique :
  ∀ {machine}
    (input : Input.InputWord machine)
    (steps : Nat) →
  WF.ExactlyOneHead (Local.cells (Guard.guardedInitialRow input steps))
guardedInitialUnique input steps =
  Character.interiorHeadIsUnique (Guard.guardedInitialInterior input steps)

guardedStandardStart :
  ∀ {machine}
    (input : Input.InputWord machine)
    (steps : Nat) →
  Standard.StandardConfiguration (Standard.standardControlOfConcrete machine)
guardedStandardStart input steps =
  Canonical.canonicalProjection (guardedInitialUnique input steps)

------------------------------------------------------------------------
-- The reverse constructor has literally one concrete edge per standard edge.
------------------------------------------------------------------------

reifiedRunLengthExact :
  ∀ {machine steps startConfiguration finishConfiguration start}
    (deterministic : Determinism.RuleKeyDeterministic machine)
    (startUnique : WF.ExactlyOneHead (Local.cells start))
    (startProjection :
      Canonical.canonicalProjection startUnique ≡ startConfiguration)
    (startMargin : Guard.Margin.HeadMargin (suc steps) (Local.cells start))
    (standardRun :
      Forward.StandardExactRun
        (Standard.standardControlOfConcrete machine)
        steps startConfiguration finishConfiguration) →
  Run.runLength
      (Reverse.concreteRun
        (Reverse.reifyStandardRun
          deterministic startUnique startProjection startMargin standardRun))
    ≡ steps
reifiedRunLengthExact deterministic startUnique startProjection startMargin
    Forward.standardRunDone = refl
reifiedRunLengthExact
    deterministic startUnique startProjection startMargin
    (Forward.standardRunStep {steps = steps} {next = next} edge rest)
  rewrite reifiedRunLengthExact
    deterministic
    (Reverse.afterUnique one)
    (Reverse.afterProjection one)
    afterMargin
    rest = refl
  where
    one : Reverse.ReifiedStandardStep startUnique next
    one = Reverse.reifyStandardStep
      deterministic startUnique (Reverse.marginOne startMargin)
      startProjection edge

    afterMargin :
      Guard.Margin.HeadMargin (suc steps) (Local.cells (Reverse.after one))
    afterMargin =
      Guard.Margin.wellFormedStepMargin (Reverse.concreteStep one) startMargin

------------------------------------------------------------------------
-- Budgeted acceptance predicates using only the existing run carriers.
------------------------------------------------------------------------

record GuardedConcreteAcceptsIn
    (machine : Local.ConcreteTapeMachine)
    (input : Input.InputWord machine)
    (steps : Nat) : Set₁ where
  field
    rows : List (Local.TapeRow machine)
    finish : Local.TapeRow machine
    certificate :
      Accepting.AcceptingWellFormedRun
        machine (Guard.guardedInitialRow input steps) rows finish
    exactLength : Accepting.acceptingRunLength certificate ≡ steps

open GuardedConcreteAcceptsIn public

record GuardedStandardAcceptsIn
    (machine : Local.ConcreteTapeMachine)
    (input : Input.InputWord machine)
    (steps : Nat) : Set₁ where
  field
    finish : Standard.StandardConfiguration
      (Standard.standardControlOfConcrete machine)
    run : Forward.StandardExactRun
      (Standard.standardControlOfConcrete machine)
      steps (guardedStandardStart input steps) finish
    accepting : Standard.standardAccepting finish

open GuardedStandardAcceptsIn public

------------------------------------------------------------------------
-- Concrete -> standard, exact same budget.
------------------------------------------------------------------------

guardedConcreteToStandard :
  ∀ {machine input steps} →
  Determinism.RuleKeyDeterministic machine →
  GuardedConcreteAcceptsIn machine input steps →
  GuardedStandardAcceptsIn machine input steps
guardedConcreteToStandard deterministic concrete
    rewrite exactLength concrete = record
  { finish = Canonical.canonicalProjection (Forward.finalUnique projected)
  ; run = Forward.runExact projected
  ; accepting = Forward.finalAccepting projected
  }
  where
    projected = Forward.projectAcceptingWellFormedRun
      deterministic (certificate concrete)

------------------------------------------------------------------------
-- Standard -> concrete, exact same budget and guarded row.
------------------------------------------------------------------------

guardedStandardToConcrete :
  ∀ {machine input steps} →
  Determinism.RuleKeyDeterministic machine →
  GuardedStandardAcceptsIn machine input steps →
  GuardedConcreteAcceptsIn machine input steps
guardedStandardToConcrete {machine} {input} {steps}
    deterministic standard = record
  { rows = Reverse.rows reified
  ; finish = Reverse.finish reified
  ; certificate = concreteCertificate
  ; exactLength =
      reifiedRunLengthExact
        deterministic startUnique refl
        (Guard.guardedInitialMargin input steps)
        (run standard)
  }
  where
    startUnique = guardedInitialUnique input steps

    reified = Reverse.reifyStandardRun
      deterministic
      startUnique
      refl
      (Guard.guardedInitialMargin input steps)
      (run standard)

    initialEndpoint :
      Accepting.InitialInteriorRow machine (Guard.guardedInitialRow input steps)
    initialEndpoint = record
      { Accepting.interior = Guard.guardedInitialInterior input steps
      ; Accepting.headIsInitial = Guard.guardedInitialState input steps
      }

    concreteCertificate :
      Accepting.AcceptingWellFormedRun
        machine
        (Guard.guardedInitialRow input steps)
        (Reverse.rows reified)
        (Reverse.finish reified)
    concreteCertificate = record
      { Accepting.initial = initialEndpoint
      ; Accepting.run = Reverse.concreteRun reified
      ; Accepting.accepting =
          Reverse.reifiedFinalAccepting reified (accepting standard)
      }

------------------------------------------------------------------------
-- Language-level iff as an explicit pair of implications.
------------------------------------------------------------------------

guardedAcceptanceIff :
  ∀ {machine input steps} →
  Determinism.RuleKeyDeterministic machine →
  (GuardedConcreteAcceptsIn machine input steps →
    GuardedStandardAcceptsIn machine input steps)
  ×
  (GuardedStandardAcceptsIn machine input steps →
    GuardedConcreteAcceptsIn machine input steps)
guardedAcceptanceIff deterministic =
  guardedConcreteToStandard deterministic ,
  guardedStandardToConcrete deterministic

------------------------------------------------------------------------
-- Finite-presentation specialization: the standard machine is definitionally
-- the same first-match control adapter as the concrete machine.
------------------------------------------------------------------------

finitePresentedGuardedAcceptanceIff :
  ∀ (presentation : Presented.FinitePresentedStandardTM)
    (input : Input.InputWord
      (Presented.finitePresentedStandardToConcrete presentation))
    (steps : Nat) →
  (GuardedConcreteAcceptsIn
      (Presented.finitePresentedStandardToConcrete presentation)
      input steps →
    GuardedStandardAcceptsIn
      (Presented.finitePresentedStandardToConcrete presentation)
      input steps)
  ×
  (GuardedStandardAcceptsIn
      (Presented.finitePresentedStandardToConcrete presentation)
      input steps →
    GuardedConcreteAcceptsIn
      (Presented.finitePresentedStandardToConcrete presentation)
      input steps)
finitePresentedGuardedAcceptanceIff presentation input steps =
  guardedAcceptanceIff
    (Presented.finitePresentedStandardToConcrete_dispatchUnique presentation)

------------------------------------------------------------------------
-- MAX-CUT STATUS
--
-- Subject to exact-head Agda certification, the ordinary machine substrate is
-- now closed through a literal guarded-input acceptance iff:
--
--   same input row
--   same first-match rule table
--   same exact T steps
--   same initial/accepting control states.
--
-- No more interpreters, alternate tape representations, or simulation clocks
-- are required for this lane. The next non-infrastructural target is the
-- algorithm-independent SAT lower-bound invariant itself.
------------------------------------------------------------------------
