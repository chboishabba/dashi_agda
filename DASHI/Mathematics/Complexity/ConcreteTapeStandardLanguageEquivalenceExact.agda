module DASHI.Mathematics.Complexity.ConcreteTapeStandardLanguageEquivalenceExact where

------------------------------------------------------------------------
-- EXACT GUARDED-INPUT ACCEPTANCE IFF
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
import DASHI.Mathematics.Complexity.ConcreteTapeHeadMarginExact as Margin
import DASHI.Mathematics.Complexity.ConcreteTapeRunCNFWeldExact as Run
import DASHI.Mathematics.Complexity.ConcreteTapeAcceptingRunCNFExact as Accepting
import DASHI.Mathematics.Complexity.PNotEqualsNPConcreteTapeRuleKeyDeterminismExact as Determinism
import DASHI.Mathematics.Complexity.StandardSingleTapeMachineExact as Standard
import DASHI.Mathematics.Complexity.ConcreteTapeStandardCanonicalProjectionExact as Canonical
import DASHI.Mathematics.Complexity.ConcreteTapeStandardRunExact as Forward
import DASHI.Mathematics.Complexity.ConcreteTapeStandardReverseRunExact as Reverse
import DASHI.Mathematics.Complexity.StandardFiniteTapePresentationExact as Presented

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
-- Exact length of the reverse constructor.
------------------------------------------------------------------------

reifiedRunLengthExact :
  ∀ {machine steps startConfiguration finishConfiguration start}
    (deterministic : Determinism.RuleKeyDeterministic machine)
    (startUnique : WF.ExactlyOneHead (Local.cells start))
    (startProjection :
      Canonical.canonicalProjection startUnique ≡ startConfiguration)
    (startMargin : Margin.HeadMargin (suc steps) (Local.cells start))
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
      Margin.HeadMargin (suc steps) (Local.cells (Reverse.after one))
    afterMargin =
      Margin.wellFormedStepMargin (Reverse.concreteStep one) startMargin

------------------------------------------------------------------------
-- Existing concrete and standard run carriers, packaged only at the language
-- boundary for the same guarded row and the same exact T-step budget.
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
      deterministic startUnique refl
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
-- Subject to exact-head Agda certification, the ordinary finite-presentation
-- machine substrate is now closed through guarded-input acceptance iff with:
-- same input row, same first-match rule table, same exact T steps, and the
-- same initial/accepting control states. The next target is therefore the
-- algorithm-independent SAT lower-bound invariant, not more machine plumbing.
------------------------------------------------------------------------
