module DASHI.Mathematics.Complexity.PNotEqualsNPVerifiedRepairedArityWidthRecurrenceExact where

------------------------------------------------------------------------
-- VERIFIED TERMINAL TREE -> REPAIRED CHARGED Q1 RECURRENCE
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Data.Empty using (⊥)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (_≤_; _<_)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.BooleanFormulaSATSelfReductionExact as SAT
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.PNotEqualsNPClayCoreExact as Clay
import DASHI.Mathematics.Complexity.PNotEqualsNPCookIndexedFormulaBridgeExact as Bridge
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1FiniteCandidateSemanticAdmissionExact as Candidate
import DASHI.Mathematics.Complexity.PNotEqualsNPFiniteCandidateRepresentativeRepairExact as Repair
import DASHI.Mathematics.Complexity.PNotEqualsNPVerifiedLocalArityTerminalAdmissionExact as Verified
import DASHI.Mathematics.Complexity.PNotEqualsNPLocalArityTerminalAdmissionExact as Local
import DASHI.Mathematics.Complexity.PNotEqualsNPRepairedArityWidthRecurrenceExact as Repaired
import DASHI.Mathematics.Complexity.PNotEqualsNPClosedStrictRepresentativeQuotientExact as Closed
import DASHI.Mathematics.Complexity.PNotEqualsNPSelfReferenceAllOverheadBudgetExact as Q1
import DASHI.Mathematics.Complexity.PNotEqualsNPBoundedSelfReferenceWellFoundedExact as Q2
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1ReachableStateRecurrenceExact as Recurrence
import DASHI.Mathematics.Complexity.PNotEqualsNPSelfDiagonalResidualWidthExact as Width
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1ExecutedConstructionMachineExact as Executed
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1FiniteCodeClayClosureExact as ClayClosure
import DASHI.Mathematics.Complexity.PNotEqualsNPPartialKleeneTerminationNoGoExact as NoGo

verifiedRepairedClosed :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (candidate : Repair.RepairedFiniteQ1Candidate root)
    (verified :
      Verified.VerifiedLocalArityTerminalAdmission
        (Repair.transitionCandidate candidate)) →
  Closed.ClosedStrictRepresentativeQuotient root
verifiedRepairedClosed candidate verified =
  Repaired.repairedClosed
    candidate
    (Local.localBuildsArityTrackedTerminalAdmission
      (Verified.verifiedBuildsLocalAdmission verified))

record VerifiedRepairedConstructionRun
    (state : Q2.BoundedSelfReferenceState) : Set₁ where
  constructor verified-repaired-construction-run
  field
    Work : Set

    advance :
      Work →
      Repaired.RepairedCandidateMachineState
        (Bridge.cookToIndexed
          (Q2.currentFormula state))
        Work

    initialWork : Work

    candidate :
      Repair.RepairedFiniteQ1Candidate
        (Bridge.cookToIndexed
          (Q2.currentFormula state))

    machineStepCount : Nat

    machineExecution :
      Executed.Iterates
        (Repaired.repairedCandidateMachineStep advance)
        machineStepCount
        (Repaired.working initialWork)
        (Repaired.finished candidate)

    verifiedAdmission :
      Verified.VerifiedLocalArityTerminalAdmission
        (Repair.transitionCandidate candidate)

    allOverheadFits :
      Q1.ClosedQuotientAllOverheadFits
        (verifiedRepairedClosed candidate verifiedAdmission)
        (Recurrence.stateOverhead state)

    machineConstructionAndNextStrict :
      (Width.triple
        (Candidate.stateCount
          (Repair.transitionCandidate candidate))
        + machineStepCount)
      +
      Q2.recursiveMeasure
        (Recurrence.q1AuthorityNextState
          state
          (verifiedRepairedClosed candidate verifiedAdmission)
          allOverheadFits)
      <
      Q2.recursiveMeasure state

open VerifiedRepairedConstructionRun public

verifiedRunToRepairedRun :
  ∀ {state : Q2.BoundedSelfReferenceState} →
  VerifiedRepairedConstructionRun state →
  Repaired.RepairedArityTerminalConstructionRun state
verifiedRunToRepairedRun run =
  Repaired.repaired-arity-terminal-construction-run
    (Work run)
    (advance run)
    (initialWork run)
    (candidate run)
    (machineStepCount run)
    (machineExecution run)
    (Local.localBuildsArityTrackedTerminalAdmission
      (Verified.verifiedBuildsLocalAdmission
        (verifiedAdmission run)))
    (allOverheadFits run)
    (machineConstructionAndNextStrict run)

VerifiedRepairedStateConstructor : Set₁
VerifiedRepairedStateConstructor =
  (state : Q2.BoundedSelfReferenceState) →
  Maybe (VerifiedRepairedConstructionRun state)

verifiedConstructorToRepaired :
  VerifiedRepairedStateConstructor →
  Repaired.RepairedArityTerminalStateConstructor
verifiedConstructorToRepaired constructor state
    with constructor state
... | nothing = nothing
... | just run = just (verifiedRunToRepairedRun run)

verifiedConstructorToQ2StepSystem :
  VerifiedRepairedStateConstructor →
  Q2.BoundedSelfReferenceStepSystem
verifiedConstructorToQ2StepSystem constructor =
  Repaired.repairedConstructorToQ2StepSystem
    (verifiedConstructorToRepaired constructor)

verifiedRepairedHighWidthBlocksRun :
  ∀ {state : Q2.BoundedSelfReferenceState}
    {next total : Nat} →
  Width.ResidualWidthStack
    {root =
      Bridge.cookToIndexed
        (Q2.currentFormula state)}
    next
    total →
  Q2.recursiveMeasure state
  ≤
  Width.triple total →
  VerifiedRepairedConstructionRun state →
  ⊥
verifiedRepairedHighWidthBlocksRun
    stack
    measureBelowWidth
    run =
  Repaired.repairedHighWidthBlocksRun
    stack
    measureBelowWidth
    (verifiedRunToRepairedRun run)

verifiedRepairedRecurrenceFiniteCodeContradictsSATInP :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    (satP : PR.InP cost Clay.SATLanguage)
    (constructor : VerifiedRepairedStateConstructor)
    (initial : Q2.BoundedSelfReferenceState) →
  ClayClosure.Q1OppositeSATTerminalSemantics
    (NoGo.satPCandidate satP)
    (verifiedConstructorToQ2StepSystem constructor)
    initial →
  ⊥
verifiedRepairedRecurrenceFiniteCodeContradictsSATInP
    satP
    constructor
    initial
    semantics =
  ClayClosure.q1FiniteCodeContradictsSATInP
    satP
    (verifiedConstructorToQ2StepSystem constructor)
    initial
    semantics

------------------------------------------------------------------------
-- On this path terminal semantic admission is now one finite Boolean verifier
-- receipt.  Existing repaired provenance/normalisation/strictness/charging and
-- the finite-code Clay compiler are reused unchanged.
------------------------------------------------------------------------
