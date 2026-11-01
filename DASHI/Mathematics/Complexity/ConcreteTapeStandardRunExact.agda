module DASHI.Mathematics.Complexity.ConcreteTapeStandardRunExact where

------------------------------------------------------------------------
-- EXACT T-STEP CONCRETE <-> CONVENTIONAL STANDARD RUN TRANSPORT
--
-- The one-step theorem is now canonical on rows.  This owner inducts over the
-- repository's existing `WellFormedTapeRun` carrier.  No new concrete run
-- semantics are introduced.  Every concrete edge becomes exactly one
-- `standardNext`, and run length is therefore preserved definitionally.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Maybe using (just)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeWellFormedConfigurationExact as WF
import DASHI.Mathematics.Complexity.ConcreteTapeLocalityCharacterizationExact as Character
import DASHI.Mathematics.Complexity.ConcreteTapeRunCNFWeldExact as Run
import DASHI.Mathematics.Complexity.ConcreteTapeAcceptingRunCNFExact as Accepting
import DASHI.Mathematics.Complexity.PNotEqualsNPConcreteTapeRuleKeyDeterminismExact as Determinism
import DASHI.Mathematics.Complexity.StandardSingleTapeMachineExact as Standard
import DASHI.Mathematics.Complexity.ConcreteTapeStandardCanonicalProjectionExact as Canonical
import DASHI.Mathematics.Complexity.ConcreteTapeStandardCanonicalOneStepExact as CanonicalStep

------------------------------------------------------------------------
-- Literal standard run relation using exactly the same step count.
------------------------------------------------------------------------

data StandardExactRun
    {State Symbol : Set}
    (machine : Standard.StandardSingleTapeMachine State Symbol) :
    Nat →
    Standard.StandardConfiguration machine →
    Standard.StandardConfiguration machine →
    Set where

  standardRunDone :
    ∀ {configuration} →
    StandardExactRun machine zero configuration configuration

  standardRunStep :
    ∀ {steps current next finish} →
    Standard.standardNext machine current ≡ just next →
    StandardExactRun machine steps next finish →
    StandardExactRun machine (suc steps) current finish

------------------------------------------------------------------------
-- Project a concrete run while retaining the final uniqueness witness needed
-- to name its canonical standard endpoint.
------------------------------------------------------------------------

record ProjectedStandardRun
    {machine : Local.ConcreteTapeMachine}
    {start rows finish}
    (startUnique : WF.ExactlyOneHead (Local.cells start))
    (concreteRun : Run.WellFormedTapeRun machine start rows finish) : Set₁ where
  field
    finalUnique : WF.ExactlyOneHead (Local.cells finish)
    standardRun :
      StandardExactRun
        (Standard.standardControlOfConcrete machine)
        (Run.runLength concreteRun)
        (Canonical.canonicalProjection startUnique)
        (Canonical.canonicalProjection finalUnique)

open ProjectedStandardRun public

projectWellFormedTapeRun :
  ∀ {machine start rows finish}
    (deterministic : Determinism.RuleKeyDeterministic machine)
    (startUnique : WF.ExactlyOneHead (Local.cells start))
    (concreteRun : Run.WellFormedTapeRun machine start rows finish) →
  ProjectedStandardRun startUnique concreteRun
projectWellFormedTapeRun deterministic startUnique Run.runDone = record
  { finalUnique = startUnique
  ; standardRun = standardRunDone
  }
projectWellFormedTapeRun
    deterministic startUnique (Run.runStep step rest) = record
  { finalUnique = finalUnique recursive
  ; standardRun =
      standardRunStep
        (CanonicalStep.canonicalWellFormedStepProjectsToStandardAnyProof
          deterministic step startUnique (WF.afterExactlyOneHead step))
        (standardRun recursive)
  }
  where
    recursive =
      projectWellFormedTapeRun
        deterministic (WF.afterExactlyOneHead step) rest

/-- There is literally one standard step for each concrete run edge. -/
projectWellFormedTapeRun_preservesLength :
  ∀ {machine start rows finish}
    (deterministic : Determinism.RuleKeyDeterministic machine)
    (startUnique : WF.ExactlyOneHead (Local.cells start))
    (concreteRun : Run.WellFormedTapeRun machine start rows finish) →
  standardRunLength
      (standardRun
        (projectWellFormedTapeRun deterministic startUnique concreteRun))
    ≡ Run.runLength concreteRun
  where
    standardRunLength :
      ∀ {State Symbol machine steps start finish} →
      StandardExactRun {State} {Symbol} machine steps start finish → Nat
    standardRunLength standardRunDone = zero
    standardRunLength (standardRunStep edge rest) =
      suc (standardRunLength rest)
projectWellFormedTapeRun_preservesLength
    deterministic startUnique Run.runDone = refl
projectWellFormedTapeRun_preservesLength
    deterministic startUnique (Run.runStep step rest)
  rewrite projectWellFormedTapeRun_preservesLength
    deterministic (WF.afterExactlyOneHead step) rest = refl

------------------------------------------------------------------------
-- Endpoint state preservation.
------------------------------------------------------------------------

canonicalProjectionInteriorState :
  ∀ {machine row}
    (interior : Character.InteriorHeadConfiguration machine row) →
  Standard.state
      (Canonical.canonicalProjection (Character.interiorHeadIsUnique interior))
    ≡ Character.headState interior
canonicalProjectionInteriorState interior =
  cong Standard.state
    (CanonicalStep.canonicalProjectionOfInterior interior)

canonicalProjectionAnyProofState :
  ∀ {machine row}
    (unique : WF.ExactlyOneHead (Local.cells row))
    (interior : Character.InteriorHeadConfiguration machine row) →
  Standard.state (Canonical.canonicalProjection unique)
    ≡ Character.headState interior
canonicalProjectionAnyProofState unique interior =
  trans
    (cong Standard.state
      (Canonical.canonicalProjectionCells-unique
        unique (Character.interiorHeadIsUnique interior)))
    (canonicalProjectionInteriorState interior)

/-- A concrete initial endpoint projects to the literal standard initial
control state. -/
concreteInitialProjectsToStandardInitial :
  ∀ {machine row}
    (unique : WF.ExactlyOneHead (Local.cells row))
    (initial : Accepting.InitialInteriorRow machine row) →
  Standard.state (Canonical.canonicalProjection unique)
    ≡ Standard.initialState (Standard.standardControlOfConcrete machine)
concreteInitialProjectsToStandardInitial unique initial =
  trans
    (canonicalProjectionAnyProofState unique (Accepting.interior initial))
    (Accepting.headIsInitial initial)

/-- A concrete accepting endpoint projects to the literal standard accepting
control state. -/
concreteAcceptingProjectsToStandardAccepting :
  ∀ {machine row}
    (unique : WF.ExactlyOneHead (Local.cells row))
    (accepting : Accepting.AcceptingInteriorRow machine row) →
  Standard.standardAccepting (Canonical.canonicalProjection unique)
concreteAcceptingProjectsToStandardAccepting unique accepting =
  trans
    (canonicalProjectionAnyProofState unique (Accepting.interior accepting))
    (Accepting.headIsAccepting accepting)

------------------------------------------------------------------------
-- Full accepting-run projection.
------------------------------------------------------------------------

record StandardAcceptingProjection
    {machine : Local.ConcreteTapeMachine}
    {start rows finish}
    (deterministic : Determinism.RuleKeyDeterministic machine)
    (certificate : Accepting.AcceptingWellFormedRun machine start rows finish) :
    Set₁ where
  field
    startUnique : WF.ExactlyOneHead (Local.cells start)
    finalUnique : WF.ExactlyOneHead (Local.cells finish)
    initialStateExact :
      Standard.state (Canonical.canonicalProjection startUnique)
      ≡ Standard.initialState (Standard.standardControlOfConcrete machine)
    runExact :
      StandardExactRun
        (Standard.standardControlOfConcrete machine)
        (Accepting.acceptingRunLength certificate)
        (Canonical.canonicalProjection startUnique)
        (Canonical.canonicalProjection finalUnique)
    finalAccepting :
      Standard.standardAccepting (Canonical.canonicalProjection finalUnique)

open StandardAcceptingProjection public

projectAcceptingWellFormedRun :
  ∀ {machine start rows finish}
    (deterministic : Determinism.RuleKeyDeterministic machine)
    (certificate : Accepting.AcceptingWellFormedRun machine start rows finish) →
  StandardAcceptingProjection deterministic certificate
projectAcceptingWellFormedRun deterministic certificate = record
  { startUnique = startU
  ; finalUnique = finalUnique projected
  ; initialStateExact =
      concreteInitialProjectsToStandardInitial
        startU (Accepting.initial certificate)
  ; runExact = standardRun projected
  ; finalAccepting =
      concreteAcceptingProjectsToStandardAccepting
        (finalUnique projected) (Accepting.accepting certificate)
  }
  where
    startU =
      Character.interiorHeadIsUnique
        (Accepting.interior (Accepting.initial certificate))
    projected =
      projectWellFormedTapeRun
        deterministic startU (Accepting.run certificate)

------------------------------------------------------------------------
-- MAX-CUT STATUS
--
-- PAID HERE (subject to exact-head Agda certification):
-- * every existing WellFormedTapeRun projects to a conventional standard run;
-- * exactly one standard step per concrete edge;
-- * exact run-length preservation;
-- * initial and accepting control-state preservation;
-- * accepting concrete runs become accepting standard runs on the same finite
--   program semantics.
--
-- REMAINING ORDINARY P INFRASTRUCTURE:
-- * package the converse run transport through the finite presentation
--   (the same rule table and one-step correspondence are already paid);
-- * state explicit polynomial clock translation using exact step identity,
--   static rule-table lookup width and existing linear T-step padding;
-- * package language equivalence and freeze this substrate.
------------------------------------------------------------------------
