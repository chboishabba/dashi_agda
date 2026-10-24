module DASHI.Mathematics.Complexity.PNotEqualsNPStagedReferenceDirectDPConstructorExact where

------------------------------------------------------------------------
-- TOTAL STAGED DIRECT-DP REFERENCE CONSTRUCTOR
--
-- CandidateDecisionVsQ1ConstructionBoundaryExact showed that the previous
-- `state -> Maybe run` interface admits an opaque always-stop implementation.
--
-- Here we implement one concrete baseline constructor:
--
--   candidate = explicit all-functions flattened Shannon automaton
--   admission = finite terminal verification tree + local arity laws
--   construction machine = one functional step from Unit to that candidate
--   evaluation charge = existing exact graph + quotient-DP cell count
--   next payload = existing one-node direct-DP authority payload
--
-- The one functional construction step is NOT advertised as a concrete tape
-- instruction trace. The expensive finite object is nevertheless charged by
-- the existing graph/evaluation cell accounting. A future restricted machine
-- may refine the one functional step and increase the construction charge.
--
-- Crucially, this constructor has no opaque stop:
--   ready(run)          iff the full displayed charge strictly fits;
--   budgetExhausted(p)  otherwise, with measure <= displayed charge.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc; zero; _+_)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (_≤_; _<_)
import Data.Nat.Properties as NatP
open import Relation.Binary.PropositionalEquality using (_≢_)
open import Relation.Nullary.Decidable.Core using (yes; no)

import DASHI.Mathematics.Complexity.PNotEqualsNPCookIndexedFormulaBridgeExact as Bridge
import DASHI.Mathematics.Complexity.PNotEqualsNPBoundedSelfReferenceWellFoundedExact as Q2
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1FiniteCandidateSemanticAdmissionExact as Candidate
import DASHI.Mathematics.Complexity.PNotEqualsNPArityTrackedTerminalSemanticAdmissionExact as ArityTerminal
import DASHI.Mathematics.Complexity.PNotEqualsNPFiniteTerminalTreeDirectDPExact as TreeDirect
import DASHI.Mathematics.Complexity.PNotEqualsNPAllFunctionsReferenceCandidateExact as Reference
import DASHI.Mathematics.Complexity.PNotEqualsNPArityTerminalDirectDPAuthorityExact as Authority
import DASHI.Mathematics.Complexity.PNotEqualsNPDirectDPChargedRecurrenceExact as DirectDP
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1ExecutedConstructionMachineExact as Executed

------------------------------------------------------------------------
-- Reference candidate/admission on one bounded state.
------------------------------------------------------------------------

referenceCandidate :
  (state : Q2.BoundedSelfReferenceState) →
  Candidate.TransitionTableCandidate
    (Bridge.cookToIndexed
      (Q2.currentFormula state))
referenceCandidate state =
  Reference.allFunctionsCandidate
    (Bridge.cookToIndexed
      (Q2.currentFormula state))

referenceAdmission :
  (state : Q2.BoundedSelfReferenceState) →
  ArityTerminal.ArityTrackedTerminalAdmission
    (referenceCandidate state)
referenceAdmission state =
  TreeDirect.treeAdmissionToArityAdmission
    (Reference.allFunctionsTreeAdmission
      (Bridge.cookToIndexed
        (Q2.currentFormula state)))

------------------------------------------------------------------------
-- Exact charge of this reference construction.
------------------------------------------------------------------------

referenceMachineStepCount : Nat
referenceMachineStepCount =
  suc zero

referenceTotalCharge :
  (state : Q2.BoundedSelfReferenceState) →
  Nat
referenceTotalCharge state =
  (Authority.arityTerminalEvaluationCellCount
      (referenceCandidate state)
      (referenceAdmission state)
    + referenceMachineStepCount)
  +
  DirectDP.directDPAuthorityPayloadMeasure
    state
    (referenceCandidate state)
    (referenceAdmission state)

------------------------------------------------------------------------
-- Literal one-step functional construction execution.
------------------------------------------------------------------------

referenceAdvance :
  (state : Q2.BoundedSelfReferenceState) →
  ⊤ →
  DirectDP.DirectDPMachineState
    (Bridge.cookToIndexed
      (Q2.currentFormula state))
    ⊤
referenceAdvance state unit =
  DirectDP.finished
    (referenceCandidate state)

referenceExecution :
  (state : Q2.BoundedSelfReferenceState) →
  Executed.Iterates
    (DirectDP.directDPMachineStep
      (referenceAdvance state))
    referenceMachineStepCount
    (DirectDP.working tt)
    (DirectDP.finished
      (referenceCandidate state))
referenceExecution state =
  Executed.iteratesStep
    Executed.iteratesZero

------------------------------------------------------------------------
-- Total staged result.
------------------------------------------------------------------------

data ReferenceDirectDPStage
    (state : Q2.BoundedSelfReferenceState) : Set₁ where

  referenceReady :
    DirectDP.DirectDPChargedConstructionRun state →
    ReferenceDirectDPStage state

  referenceBudgetExhausted :
    Q2.recursiveMeasure state
    ≤
    referenceTotalCharge state →
    ReferenceDirectDPStage state

stagedReferenceDirectDP :
  (state : Q2.BoundedSelfReferenceState) →
  ReferenceDirectDPStage state
stagedReferenceDirectDP state
    with NatP._<?_
      (referenceTotalCharge state)
      (Q2.recursiveMeasure state)
... | yes fits =
  referenceReady
    (DirectDP.direct-dp-charged-construction-run
      ⊤
      (referenceAdvance state)
      tt
      (referenceCandidate state)
      referenceMachineStepCount
      (referenceExecution state)
      (referenceAdmission state)
      fits)
... | no doesNotFit =
  referenceBudgetExhausted
    (NatP.≮⇒≥ doesNotFit)

------------------------------------------------------------------------
-- Maybe projection for compatibility with the legacy constructor interface.
------------------------------------------------------------------------

stageToMaybeRun :
  ∀ {state : Q2.BoundedSelfReferenceState} →
  ReferenceDirectDPStage state →
  Maybe (DirectDP.DirectDPChargedConstructionRun state)
stageToMaybeRun (referenceReady run) =
  just run
stageToMaybeRun (referenceBudgetExhausted exhausted) =
  nothing

referenceDirectDPConstructor :
  DirectDP.DirectDPChargedStateConstructor
referenceDirectDPConstructor state =
  stageToMaybeRun
    (stagedReferenceDirectDP state)

------------------------------------------------------------------------
-- Exact success/failure characterization.
------------------------------------------------------------------------

referenceChargeFitGivesProgress :
  (state : Q2.BoundedSelfReferenceState) →
  referenceTotalCharge state
  <
  Q2.recursiveMeasure state →
  referenceDirectDPConstructor state
  ≢
  nothing
referenceChargeFitGivesProgress state fits
    with NatP._<?_
      (referenceTotalCharge state)
      (Q2.recursiveMeasure state)
... | yes actualFits =
  λ ()
... | no doesNotFit =
  ⊥-elim (doesNotFit fits)

referenceChargeExhaustionForcesStop :
  (state : Q2.BoundedSelfReferenceState) →
  Q2.recursiveMeasure state
  ≤
  referenceTotalCharge state →
  referenceDirectDPConstructor state
  ≡
  nothing
referenceChargeExhaustionForcesStop state exhausted
    with NatP._<?_
      (referenceTotalCharge state)
      (Q2.recursiveMeasure state)
... | yes fits =
  ⊥-elim (NatP.<⇒≱ fits exhausted)
... | no doesNotFit =
  refl

------------------------------------------------------------------------
-- FRONTIER CONSEQUENCE
--
-- We now have an ACTUAL non-opaque DirectDP constructor. For the all-functions
-- baseline, first-step progress is reduced exactly to one arithmetic question:
--
--   referenceTotalCharge(state) < recursiveMeasure(state).
--
-- Because the reference state space contains every Boolean function, this is
-- expected to fail quickly. The root-reachable quotient path must beat this
-- charge; the special candidate/self-code theorem must explain why a cheaper
-- construction exists or why every legitimate construction still collides
-- with the semantic-width lower bound.
------------------------------------------------------------------------
