module DASHI.Mathematics.Complexity.PNotEqualsNPRepairedArityWidthRecurrenceExact where

------------------------------------------------------------------------
-- REPAIRED ARITY-TRACKED Q1 RECURRENCE + SEMANTIC-WIDTH CHARGE
--
-- This is the non-vacuous replacement for the old FiniteQ1Candidate path.
--
-- Raw Shannon descendants carry provenance only.  Evaluator-verified rewrite
-- programs produce one-node strict representatives.  Arity/terminal admission
-- still acts on the SAME finite transition table, so the residual-width
-- injection theorem is unchanged.
--
-- A successful repaired run pays:
--
--   transition graph cells = 3 * stateCount
--   + explicit machine step count
--   + measure(next repaired authority state)
--   < measure(current).
--
-- Therefore any all-layer semantic width stack with
--
--   measure(current) <= 3 * summedWidth
--
-- blocks a repaired successful run exactly as intended, now on an inhabitable
-- carrier.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Data.Empty using (⊥)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (_≤_; _<_)
import Data.Nat.Properties as NatP

import DASHI.Mathematics.Complexity.BooleanFormulaSATSelfReductionExact as SAT
import DASHI.Mathematics.Complexity.PNotEqualsNPCookIndexedFormulaBridgeExact as Bridge
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1FiniteCandidateSemanticAdmissionExact as Candidate
import DASHI.Mathematics.Complexity.PNotEqualsNPArityTrackedTerminalSemanticAdmissionExact as ArityTerminal
import DASHI.Mathematics.Complexity.PNotEqualsNPFiniteCandidateRepresentativeRepairExact as Repair
import DASHI.Mathematics.Complexity.PNotEqualsNPSelfDiagonalResidualWidthExact as Width
import DASHI.Mathematics.Complexity.PNotEqualsNPSelfReferenceAllOverheadBudgetExact as Q1
import DASHI.Mathematics.Complexity.PNotEqualsNPBoundedSelfReferenceWellFoundedExact as Q2
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1ReachableStateRecurrenceExact as Recurrence

------------------------------------------------------------------------
-- Repaired closed quotient from local arity/terminal admission.
------------------------------------------------------------------------

repairedClosed :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (candidate : Repair.RepairedFiniteQ1Candidate root)
    (admission :
      ArityTerminal.ArityTrackedTerminalAdmission
        (Repair.transitionCandidate candidate)) →
  DASHI.Mathematics.Complexity.PNotEqualsNPClosedStrictRepresentativeQuotientExact.ClosedStrictRepresentativeQuotient
    root
repairedClosed candidate admission =
  Repair.repairedToClosedStrictRepresentativeQuotient
    candidate
    (ArityTerminal.arityTerminalAdmissionBuildsSemanticCongruence
      admission)

------------------------------------------------------------------------
-- One repaired successful construction run at a Q2 state.
------------------------------------------------------------------------

record RepairedArityTerminalConstructionRun
    (state : Q2.BoundedSelfReferenceState) : Set₁ where
  constructor repaired-arity-terminal-construction-run
  field
    candidate :
      Repair.RepairedFiniteQ1Candidate
        (Bridge.cookToIndexed
          (Q2.currentFormula state))

    localAdmission :
      ArityTerminal.ArityTrackedTerminalAdmission
        (Repair.transitionCandidate candidate)

    allOverheadFits :
      Q1.ClosedQuotientAllOverheadFits
        (repairedClosed candidate localAdmission)
        (Recurrence.stateOverhead state)

    machineStepCount :
      Nat

    machineConstructionAndNextStrict :
      (Width.triple
        (Candidate.stateCount
          (Repair.transitionCandidate candidate))
        + machineStepCount)
      +
      Q2.recursiveMeasure
        (Recurrence.q1AuthorityNextState
          state
          (repairedClosed candidate localAdmission)
          allOverheadFits)
      <
      Q2.recursiveMeasure state

open RepairedArityTerminalConstructionRun public

------------------------------------------------------------------------
-- The actual next state and its strict decrease.
------------------------------------------------------------------------

repairedNextState :
  ∀ {state : Q2.BoundedSelfReferenceState} →
  RepairedArityTerminalConstructionRun state →
  Q2.BoundedSelfReferenceState
repairedNextState {state} run =
  Recurrence.q1AuthorityNextState
    state
    (repairedClosed
      (candidate run)
      (localAdmission run))
    (allOverheadFits run)

repairedNextStateStrictlyDecreases :
  ∀ {state : Q2.BoundedSelfReferenceState}
    (run : RepairedArityTerminalConstructionRun state) →
  Q2.recursiveMeasure
      (repairedNextState run)
  <
  Q2.recursiveMeasure state
repairedNextStateStrictlyDecreases {state} run =
  NatP.≤-<-trans
    nextBelowCharged
    (machineConstructionAndNextStrict run)
  where
    graphAndMachine :
      Nat
    graphAndMachine =
      Width.triple
        (Candidate.stateCount
          (Repair.transitionCandidate
            (candidate run)))
      + machineStepCount run

    nextBelowCharged :
      Q2.recursiveMeasure
          (repairedNextState run)
      ≤
      graphAndMachine
        +
      Q2.recursiveMeasure
          (repairedNextState run)
    nextBelowCharged =
      NatP.n≤m+n
        (Q2.recursiveMeasure
          (repairedNextState run))
        graphAndMachine

------------------------------------------------------------------------
-- All-layer semantic width still injects into this repaired transition table.
------------------------------------------------------------------------

repairedLayeredWidthBelowStateCount :
  ∀ {state : Q2.BoundedSelfReferenceState}
    {next total : Nat}
    (run : RepairedArityTerminalConstructionRun state) →
  Width.ResidualWidthStack
    {root =
      Bridge.cookToIndexed
        (Q2.currentFormula state)}
    next
    total →
  total
  ≤
  Candidate.stateCount
    (Repair.transitionCandidate
      (candidate run))
repairedLayeredWidthBelowStateCount run stack =
  Width.layeredResidualWidthSumBelowCandidateStateCount
    (localAdmission run)
    stack

------------------------------------------------------------------------
-- Charge 3 cells per required semantic state against the repaired run.
------------------------------------------------------------------------

repairedTripleLayeredWidthPlusNextStrict :
  ∀ {state : Q2.BoundedSelfReferenceState}
    {next total : Nat}
    (run : RepairedArityTerminalConstructionRun state) →
  Width.ResidualWidthStack
    {root =
      Bridge.cookToIndexed
        (Q2.currentFormula state)}
    next
    total →
  Width.triple total
    +
    Q2.recursiveMeasure
      (repairedNextState run)
  <
  Q2.recursiveMeasure state
repairedTripleLayeredWidthPlusNextStrict
    {state}
    run
    stack =
  NatP.≤-<-trans
    widthAndNextBelowCharged
    (machineConstructionAndNextStrict run)
  where
    stateCount :
      Nat
    stateCount =
      Candidate.stateCount
        (Repair.transitionCandidate
          (candidate run))

    widthBelowStateCount :
      total ≤ stateCount
    widthBelowStateCount =
      repairedLayeredWidthBelowStateCount
        run
        stack

    tripleWidthBelowGraph :
      Width.triple total
      ≤
      Width.triple stateCount
    tripleWidthBelowGraph =
      Width.tripleMonotone
        widthBelowStateCount

    tripleWidthBelowGraphAndMachine :
      Width.triple total
      ≤
      Width.triple stateCount
        + machineStepCount run
    tripleWidthBelowGraphAndMachine =
      NatP.≤-trans
        tripleWidthBelowGraph
        (NatP.m≤m+n
          (Width.triple stateCount)
          (machineStepCount run))

    widthAndNextBelowCharged :
      Width.triple total
        +
        Q2.recursiveMeasure
          (repairedNextState run)
      ≤
      (Width.triple stateCount
        + machineStepCount run)
        +
        Q2.recursiveMeasure
          (repairedNextState run)
    widthAndNextBelowCharged =
      NatP.+-mono-≤
        tripleWidthBelowGraphAndMachine
        NatP.≤-refl

repairedTripleLayeredWidthStrictlyBelowCurrentMeasure :
  ∀ {state : Q2.BoundedSelfReferenceState}
    {next total : Nat}
    (run : RepairedArityTerminalConstructionRun state) →
  Width.ResidualWidthStack
    {root =
      Bridge.cookToIndexed
        (Q2.currentFormula state)}
    next
    total →
  Width.triple total
  <
  Q2.recursiveMeasure state
repairedTripleLayeredWidthStrictlyBelowCurrentMeasure
    run
    stack =
  NatP.<-≤-trans
    (NatP.m≤m+n
      (Width.triple _)
      (Q2.recursiveMeasure
        (repairedNextState run)))
    (repairedTripleLayeredWidthPlusNextStrict
      run
      stack)

------------------------------------------------------------------------
-- Direct non-vacuous high-width obstruction.
------------------------------------------------------------------------

repairedHighWidthBlocksRun :
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
  RepairedArityTerminalConstructionRun state →
  ⊥
repairedHighWidthBlocksRun
    stack
    measureBelowWidth
    run =
  NatP.<⇒≱
    (repairedTripleLayeredWidthStrictlyBelowCurrentMeasure
      run
      stack)
    measureBelowWidth

------------------------------------------------------------------------
-- Total Maybe constructor and repaired Q2 step system.
------------------------------------------------------------------------

RepairedArityTerminalStateConstructor : Set₁
RepairedArityTerminalStateConstructor =
  (state : Q2.BoundedSelfReferenceState) →
  Maybe (RepairedArityTerminalConstructionRun state)

repairedNext :
  RepairedArityTerminalStateConstructor →
  Q2.BoundedSelfReferenceState →
  Maybe Q2.BoundedSelfReferenceState
repairedNext constructor state
    with constructor state
... | nothing =
  nothing
... | just run =
  just (repairedNextState run)

justInjective :
  ∀ {A : Set} {left right : A} →
  just left ≡ just right →
  left ≡ right
justInjective refl =
  refl

repairedNextStrictlyDecreases :
  (constructor : RepairedArityTerminalStateConstructor) →
  (state nextState : Q2.BoundedSelfReferenceState) →
  repairedNext constructor state
  ≡
  just nextState →
  Q2.recursiveMeasure nextState
  <
  Q2.recursiveMeasure state
repairedNextStrictlyDecreases
    constructor
    state
    nextState
    equation
    with constructor state
... | nothing =
  caseNothing equation
  where
    caseNothing :
      nothing ≡ just nextState →
      Q2.recursiveMeasure nextState
      <
      Q2.recursiveMeasure state
    caseNothing ()
... | just run =
  substTarget
    (justInjective equation)
    (repairedNextStateStrictlyDecreases run)
  where
    substTarget :
      ∀ {left right : Q2.BoundedSelfReferenceState} →
      left ≡ right →
      Q2.recursiveMeasure left
        <
      Q2.recursiveMeasure state →
      Q2.recursiveMeasure right
        <
      Q2.recursiveMeasure state
    substTarget refl proof =
      proof

repairedConstructorToQ2StepSystem :
  RepairedArityTerminalStateConstructor →
  Q2.BoundedSelfReferenceStepSystem
repairedConstructorToQ2StepSystem constructor =
  Q2.bounded-self-reference-step-system
    (repairedNext constructor)
    (repairedNextStrictlyDecreases constructor)

------------------------------------------------------------------------
-- FRONTIER CONSEQUENCE
--
-- The width-vs-resource experiment is restored on a non-vacuous carrier.
-- What remains is now genuinely mathematical/algorithmic:
--
--   * construct repaired candidates for the actual live roots;
--   * or construct a width stack violating their charged budget.
--
-- The previous raw-restriction strictness bug is no longer part of that search.
------------------------------------------------------------------------
