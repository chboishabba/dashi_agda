module DASHI.Mathematics.Complexity.ConcreteTapeStandardReverseRunExact where

------------------------------------------------------------------------
-- GUARDED CONVENTIONAL STANDARD RUN -> LITERAL CONCRETE RUN
--
-- This is the missing converse to ConcreteTapeStandardRunExact.
--
-- A standard run is reified from a concrete row whose canonical projection is
-- the standard start configuration and whose head has T+1 cells of margin on
-- each side.  At each edge we inspect the SAME first-match rule lookup used by
-- `standardControlOfConcrete`:
--
-- * `nothing` contradicts the given successful standard edge;
-- * `just rule` is executed by the existing proof-producing concrete executor;
-- * canonical one-step preservation forces the concrete successor projection
--   to be exactly the supplied standard successor.
--
-- The existing head-margin theorem consumes at most one cell per step, so the
-- induction closes with one cell of margin at the final row.  No new machine,
-- transition, or run semantics are introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Maybe using (nothing; just)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Nat.Base using (_≤_; z≤n; s≤s)
open import Data.Product using (Σ; _,_; _×_)
open import Relation.Binary.PropositionalEquality using (sym; trans; cong)

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeWellFormedConfigurationExact as WF
import DASHI.Mathematics.Complexity.ConcreteTapeLocalityCharacterizationExact as Character
import DASHI.Mathematics.Complexity.ConcreteTapeHeadMarginExact as Margin
import DASHI.Mathematics.Complexity.ConcreteTapeRunCNFWeldExact as Run
import DASHI.Mathematics.Complexity.ConcreteTapeAcceptingRunCNFExact as Accepting
import DASHI.Mathematics.Complexity.PNotEqualsNPConcreteTapeExecutableRelationalEquivalenceExact as Execute
import DASHI.Mathematics.Complexity.PNotEqualsNPConcreteTapeRuleKeyDeterminismExact as Determinism
import DASHI.Mathematics.Complexity.StandardSingleTapeMachineExact as Standard
import DASHI.Mathematics.Complexity.ConcreteTapeStandardOneStepExact as OneStep
import DASHI.Mathematics.Complexity.ConcreteTapeStandardCanonicalProjectionExact as Canonical
import DASHI.Mathematics.Complexity.ConcreteTapeStandardCanonicalOneStepExact as CanonicalStep
import DASHI.Mathematics.Complexity.ConcreteTapeStandardRunExact as Forward
import DASHI.Mathematics.Complexity.StandardFiniteTapePresentationExact as Presented

------------------------------------------------------------------------
-- Elementary margin weakening to the one-cell interiority threshold.
------------------------------------------------------------------------

marginOne :
  ∀ {State Symbol : Set} {k : Nat}
    {cells : List (Local.TapeCell State Symbol)} →
  Margin.HeadMargin (suc k) cells →
  Margin.HeadMargin 1 cells
marginOne {k = k} margin = record
  { Margin.leftMargin =
      ≤-trans-local (s≤s z≤n) (Margin.leftMargin margin)
  ; Margin.rightMargin =
      ≤-trans-local (s≤s z≤n) (Margin.rightMargin margin)
  }
  where
    ≤-trans-local : ∀ {a b c : Nat} → a ≤ b → b ≤ c → a ≤ c
    ≤-trans-local z≤n _ = z≤n
    ≤-trans-local (s≤s p) (s≤s q) = s≤s (≤-trans-local p q)

------------------------------------------------------------------------
-- A successful standard edge forces the concrete executor to succeed.
------------------------------------------------------------------------

standardEdgeForcesConcreteExecution :
  ∀ {machine before next}
    (interior : Character.InteriorHeadConfiguration machine before) →
  Standard.standardNext
      (Standard.standardControlOfConcrete machine)
      (OneStep.standardBeforeOfInterior interior)
    ≡ just next →
  Σ (Local.TapeRow machine)
    (λ after → Execute.executeInteriorAfter interior ≡ just after)
standardEdgeForcesConcreteExecution {machine} interior edge
    with Character.rowShape interior
... | refl
    with DASHI.Mathematics.Complexity.PNotEqualsNPConcreteTapeRuleTableInterpreterExact.fetchConcreteRule
      machine
      (Character.headState interior)
      (Character.readSymbol interior)
...   | nothing
      with edge
...     | ()
...   | just matched =
  _ , refl

------------------------------------------------------------------------
-- One standard edge reifies to one literal WellFormedMachineStep.
------------------------------------------------------------------------

record ReifiedStandardStep
    {machine : Local.ConcreteTapeMachine}
    {before : Local.TapeRow machine}
    (beforeUnique : WF.ExactlyOneHead (Local.cells before))
    (next : Standard.StandardConfiguration
      (Standard.standardControlOfConcrete machine)) : Set₁ where
  field
    after : Local.TapeRow machine
    concreteStep : WF.WellFormedMachineStep machine before after
    afterUnique : WF.ExactlyOneHead (Local.cells after)
    afterProjection :
      Canonical.canonicalProjection afterUnique ≡ next

open ReifiedStandardStep public

reifyStandardStep :
  ∀ {machine before current next}
    (deterministic : Determinism.RuleKeyDeterministic machine)
    (beforeUnique : WF.ExactlyOneHead (Local.cells before))
    (beforeMargin : Margin.HeadMargin 1 (Local.cells before))
    (beforeProjection : Canonical.canonicalProjection beforeUnique ≡ current)
    (edge : Standard.standardNext
      (Standard.standardControlOfConcrete machine) current ≡ just next) →
  ReifiedStandardStep beforeUnique next
reifyStandardStep
    {machine} {before} {current} {next}
    deterministic beforeUnique beforeMargin beforeProjection edge =
  record
    { after = chosenAfter
    ; concreteStep = chosenStep
    ; afterUnique = chosenAfterUnique
    ; afterProjection = projectionExact
    }
  where
    interior : Character.InteriorHeadConfiguration machine before
    interior = Margin.interiorFromUniqueMargin beforeUnique beforeMargin

    intrinsicProjection :
      OneStep.standardBeforeOfInterior interior ≡ current
    intrinsicProjection =
      trans
        (sym (CanonicalStep.canonicalProjectionOfInterior interior))
        (trans
          (Canonical.canonicalProjectionCells-unique
            (Character.interiorHeadIsUnique interior) beforeUnique)
          beforeProjection)

    intrinsicEdge :
      Standard.standardNext
        (Standard.standardControlOfConcrete machine)
        (OneStep.standardBeforeOfInterior interior)
      ≡ just next
    intrinsicEdge =
      trans
        (cong
          (Standard.standardNext
            (Standard.standardControlOfConcrete machine))
          intrinsicProjection)
        edge

    execution = standardEdgeForcesConcreteExecution interior intrinsicEdge
    chosenAfter = Data.Product.proj₁ execution
    executionExact = Data.Product.proj₂ execution

    chosenStep : WF.WellFormedMachineStep machine before chosenAfter
    chosenStep = Execute.executeInteriorAfterSound interior executionExact

    chosenAfterUnique : WF.ExactlyOneHead (Local.cells chosenAfter)
    chosenAfterUnique = WF.afterExactlyOneHead chosenStep

    projectedEdge :
      Standard.standardNext
        (Standard.standardControlOfConcrete machine)
        (Canonical.canonicalProjection beforeUnique)
      ≡ just (Canonical.canonicalProjection chosenAfterUnique)
    projectedEdge =
      CanonicalStep.canonicalWellFormedStepProjectsToStandardAnyProof
        deterministic chosenStep beforeUnique chosenAfterUnique

    projectedEdgeAtCurrent :
      Standard.standardNext
        (Standard.standardControlOfConcrete machine) current
      ≡ just (Canonical.canonicalProjection chosenAfterUnique)
    projectedEdgeAtCurrent =
      trans
        (cong
          (Standard.standardNext
            (Standard.standardControlOfConcrete machine))
          (sym beforeProjection))
        projectedEdge

    justOutputsEqual :
      just (Canonical.canonicalProjection chosenAfterUnique) ≡ just next
    justOutputsEqual = trans (sym projectedEdgeAtCurrent) edge

    projectionExact :
      Canonical.canonicalProjection chosenAfterUnique ≡ next
    projectionExact
      with justOutputsEqual
    ... | refl = refl

------------------------------------------------------------------------
-- T+1-margin induction over the existing StandardExactRun.
------------------------------------------------------------------------

record ReifiedStandardRun
    {machine : Local.ConcreteTapeMachine}
    {steps : Nat}
    {standardStart standardFinish :
      Standard.StandardConfiguration
        (Standard.standardControlOfConcrete machine)}
    (start : Local.TapeRow machine)
    (startUnique : WF.ExactlyOneHead (Local.cells start))
    (standardRun :
      Forward.StandardExactRun
        (Standard.standardControlOfConcrete machine)
        steps standardStart standardFinish) : Set₁ where
  field
    rows : List (Local.TapeRow machine)
    finish : Local.TapeRow machine
    concreteRun : Run.WellFormedTapeRun machine start rows finish
    finalUnique : WF.ExactlyOneHead (Local.cells finish)
    finalProjection :
      Canonical.canonicalProjection finalUnique ≡ standardFinish
    finalMargin : Margin.HeadMargin 1 (Local.cells finish)

open ReifiedStandardRun public

reifyStandardRun :
  ∀ {machine steps standardStart standardFinish start}
    (deterministic : Determinism.RuleKeyDeterministic machine)
    (startUnique : WF.ExactlyOneHead (Local.cells start))
    (startProjection :
      Canonical.canonicalProjection startUnique ≡ standardStart)
    (startMargin : Margin.HeadMargin (suc steps) (Local.cells start))
    (standardRun :
      Forward.StandardExactRun
        (Standard.standardControlOfConcrete machine)
        steps standardStart standardFinish) →
  ReifiedStandardRun start startUnique standardRun
reifyStandardRun deterministic startUnique startProjection startMargin
    Forward.standardRunDone =
  record
    { rows = []
    ; finish = _
    ; concreteRun = Run.runDone
    ; finalUnique = startUnique
    ; finalProjection = startProjection
    ; finalMargin = startMargin
    }
reifyStandardRun
    deterministic startUnique startProjection startMargin
    (Forward.standardRunStep {steps = steps} {current = current}
      {next = next} edge rest) =
  record
    { rows = ReifiedStandardStep.after one ∷ ReifiedStandardRun.rows recursive
    ; finish = ReifiedStandardRun.finish recursive
    ; concreteRun =
        Run.runStep
          (ReifiedStandardStep.concreteStep one)
          (ReifiedStandardRun.concreteRun recursive)
    ; finalUnique = ReifiedStandardRun.finalUnique recursive
    ; finalProjection = ReifiedStandardRun.finalProjection recursive
    ; finalMargin = ReifiedStandardRun.finalMargin recursive
    }
  where
    one : ReifiedStandardStep startUnique next
    one =
      reifyStandardStep
        deterministic
        startUnique
        (marginOne startMargin)
        startProjection
        edge

    afterMargin :
      Margin.HeadMargin (suc steps)
        (Local.cells (ReifiedStandardStep.after one))
    afterMargin =
      Margin.wellFormedStepMargin
        (ReifiedStandardStep.concreteStep one)
        startMargin

    recursive =
      reifyStandardRun
        deterministic
        (ReifiedStandardStep.afterUnique one)
        (ReifiedStandardStep.afterProjection one)
        afterMargin
        rest

/-- The converse preserves the literal step count: one concrete run edge is
constructed for every standard edge. -/
reifyStandardRun_preservesLength :
  ∀ {machine steps standardStart standardFinish start}
    (deterministic : Determinism.RuleKeyDeterministic machine)
    (startUnique : WF.ExactlyOneHead (Local.cells start))
    (startProjection :
      Canonical.canonicalProjection startUnique ≡ standardStart)
    (startMargin : Margin.HeadMargin (suc steps) (Local.cells start))
    (standardRun :
      Forward.StandardExactRun
        (Standard.standardControlOfConcrete machine)
        steps standardStart standardFinish) →
  Run.runLength
      (ReifiedStandardRun.concreteRun
        (reifyStandardRun deterministic startUnique startProjection
          startMargin standardRun))
    ≡ steps
reifyStandardRun_preservesLength
    deterministic startUnique startProjection startMargin
    Forward.standardRunDone = refl
reifyStandardRun_preservesLength
    deterministic startUnique startProjection startMargin
    (Forward.standardRunStep edge rest)
  rewrite reifyStandardRun_preservesLength
    deterministic
    (ReifiedStandardStep.after
      (reifyStandardStep deterministic startUnique (marginOne startMargin)
        startProjection edge)
      |> λ _ → ReifiedStandardStep.afterUnique
        (reifyStandardStep deterministic startUnique (marginOne startMargin)
          startProjection edge))
    (ReifiedStandardStep.afterProjection
      (reifyStandardStep deterministic startUnique (marginOne startMargin)
        startProjection edge))
    (Margin.wellFormedStepMargin
      (ReifiedStandardStep.concreteStep
        (reifyStandardStep deterministic startUnique (marginOne startMargin)
          startProjection edge))
      startMargin)
    rest = refl

------------------------------------------------------------------------
-- Acceptance endpoint transport.
------------------------------------------------------------------------

reifiedFinalAccepting :
  ∀ {machine steps standardStart standardFinish start}
    {startUnique : WF.ExactlyOneHead (Local.cells start)}
    {standardRun :
      Forward.StandardExactRun
        (Standard.standardControlOfConcrete machine)
        steps standardStart standardFinish}
    (reified : ReifiedStandardRun start startUnique standardRun) →
  Standard.standardAccepting standardFinish →
  Accepting.AcceptingInteriorRow machine (ReifiedStandardRun.finish reified)
reifiedFinalAccepting reified standardAccepting = record
  { Accepting.interior = finalInterior
  ; Accepting.headIsAccepting = headAccepting
  }
  where
    finalInterior =
      Margin.interiorFromUniqueMargin
        (ReifiedStandardRun.finalUnique reified)
        (ReifiedStandardRun.finalMargin reified)

    projectionState :
      Standard.state
        (Canonical.canonicalProjection
          (ReifiedStandardRun.finalUnique reified))
      ≡ Character.headState finalInterior
    projectionState =
      Forward.canonicalProjectionAnyProofState
        (ReifiedStandardRun.finalUnique reified) finalInterior

    headAccepting :
      Character.headState finalInterior ≡ Local.acceptingState _
    headAccepting =
      trans
        (sym projectionState)
        (trans
          (cong Standard.state (ReifiedStandardRun.finalProjection reified))
          standardAccepting)

------------------------------------------------------------------------
-- Finite-presentation specialization: the standard machine here is
-- definitionally the same first-match control adapter as the concrete machine.
------------------------------------------------------------------------

reifyFinitePresentedStandardRun :
  ∀ {steps standardStart standardFinish}
    (presentation : Presented.FinitePresentedStandardTM)
    (start : Local.TapeRow
      (Presented.finitePresentedStandardToConcrete presentation))
    (startUnique : WF.ExactlyOneHead (Local.cells start))
    (startProjection :
      Canonical.canonicalProjection startUnique ≡ standardStart)
    (startMargin : Margin.HeadMargin (suc steps) (Local.cells start))
    (standardRun :
      Forward.StandardExactRun
        (Presented.finitePresentedStandardMachine presentation)
        steps standardStart standardFinish) →
  ReifiedStandardRun start startUnique standardRun
reifyFinitePresentedStandardRun presentation =
  reifyStandardRun
    (Presented.finitePresentedStandardToConcrete_dispatchUnique presentation)

------------------------------------------------------------------------
-- MAX-CUT STATUS
--
-- PAID HERE, subject to exact-head Agda certification:
-- * one successful standard edge reifies through the literal first-match
--   executor to one WellFormedMachineStep;
-- * canonical successor projection is exactly the supplied standard successor;
-- * a T-step run reifies with T+1 initial head margin;
-- * the reverse transport preserves step count exactly;
-- * the final row retains one-cell margin and standard acceptance transports
--   to the literal concrete accepting endpoint predicate;
-- * the theorem specializes definitionally to FinitePresentedStandardTM.
--
-- The remaining language wrapper is now only input-endpoint packaging:
-- identify the canonical standard input configuration with the existing
-- `guardedInitialRow input T`, combine this reverse theorem with
-- `projectAcceptingWellFormedRun`, and state the resulting acceptance iff.
-- No further transition/run representation machinery is required.
------------------------------------------------------------------------
