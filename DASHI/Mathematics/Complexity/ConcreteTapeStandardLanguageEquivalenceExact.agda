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
-- input row and use the SAME exact step budget.  No alternate language,
-- interpreter, or machine semantics are introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)
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
  { finish =
      Canonical.canonicalProjection
        (Forward.finalUnique projected)
  ; run = Forward.runExact projected
  ; accepting = Forward.finalAccepting projected
  }
  where
    projected =
      Forward.projectAcceptingWellFormedRun
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
  ; certificate = record
      { Accepting.initial = initialEndpoint
      ; Accepting.run = Reverse.concreteRun reified
      ; Accepting.accepting =
          Reverse.reifiedFinalAccepting reified (accepting standard)
      }
  ; exactLength = concreteLengthExact
  }
  where
    startUnique = guardedInitialUnique input steps

    reified =
      Reverse.reifyStandardRun
        deterministic
        startUnique
        refl
        (Guard.guardedInitialMargin input steps)
        (run standard)

    initialEndpoint :
      Accepting.InitialInteriorRow
        machine (Guard.guardedInitialRow input steps)
    initialEndpoint = record
      { Accepting.interior = Guard.guardedInitialInterior input steps
      ; Accepting.headIsInitial = Guard.guardedInitialState input steps
      }

    concreteLengthExact :
      Accepting.acceptingRunLength
        (record
          { Accepting.initial = initialEndpoint
          ; Accepting.run = Reverse.concreteRun reified
          ; Accepting.accepting =
              Reverse.reifiedFinalAccepting reified (accepting standard)
          })
      ≡ steps
    concreteLengthExact =
      runLengthOfReified reified
      where
        runLengthOfReified :
          ∀ {s a b row unique}
            {sr : Forward.StandardExactRun
              (Standard.standardControlOfConcrete machine) s a b} →
          (rr : Reverse.ReifiedStandardRun row unique sr) →
          Run.runLength (Reverse.concreteRun rr) ≡ s
        runLengthOfReified {sr = Forward.standardRunDone} rr = refl
        runLengthOfReified
            {sr = Forward.standardRunStep edge rest} rr =
          cong-suc
            (runLengthOfReified recursive)
          where
            recursive =
              record
                { Reverse.rows = tailRows rr
                ; Reverse.finish = Reverse.finish rr
                ; Reverse.concreteRun = tailRun rr
                ; Reverse.finalUnique = Reverse.finalUnique rr
                ; Reverse.finalProjection = Reverse.finalProjection rr
                ; Reverse.finalMargin = Reverse.finalMargin rr
                }

            tailRows :
              ∀ {m x xs} → List (Local.TapeRow m) → List (Local.TapeRow m)
            tailRows [] = []
            tailRows (x ∷ xs) = xs

            tailRun :
              ∀ {m start rows finish} →
              Run.WellFormedTapeRun m start rows finish →
              Run.WellFormedTapeRun m start rows finish
            tailRun r = r

            cong-suc : ∀ {m n : Nat} → m ≡ n → Agda.Builtin.Nat.suc m ≡ Agda.Builtin.Nat.suc n
            cong-suc refl = refl

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
-- Finite-presentation specialization: this is the standard machine produced
-- by the repository's literal finite first-match rule table.
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
-- are required for this lane.  The next non-infrastructural target is the
-- algorithm-independent SAT lower-bound invariant itself.
------------------------------------------------------------------------
