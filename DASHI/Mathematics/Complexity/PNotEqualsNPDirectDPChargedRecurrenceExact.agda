module DASHI.Mathematics.Complexity.PNotEqualsNPDirectDPChargedRecurrenceExact where

------------------------------------------------------------------------
-- DIRECT DP AUTHORITY: CHARGED RECURRENCE
--
-- Live Q1 data are now only:
--
--   * a finite transition table;
--   * a typed machine execution that emits it;
--   * local arity/terminal admission.
--
-- The existing quotient DP computes the exact root SAT bit.  The next Q2
-- formula is the resulting one-node Cook constant authority.
--
-- Exact live-step charge:
--
--   quotientEvaluationCellCount
--     + machineStepCount
--     + nextSelfReferencePayload
--     < recursiveMeasure(current)
--
-- where quotientEvaluationCellCount already contains
--
--   3 * stateCount + (n+1) * stateCount.
--
-- This is the minimal non-vacuous resource carrier for the residual-width
-- falsification experiment.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Data.Empty using (⊥)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (_≤_; _<_)
import Data.Nat.Properties as NatP

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.BooleanFormulaSATSelfReductionExact as SAT
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.PNotEqualsNPClayCoreExact as Clay
import DASHI.Mathematics.Complexity.PNotEqualsNPCookIndexedFormulaBridgeExact as Bridge
import DASHI.Mathematics.Complexity.PNotEqualsNPProgramDescriptionFormulaEmbeddingExact as Size
import DASHI.Mathematics.Complexity.PNotEqualsNPResourceClosingRestrictionQuotientExact as Quotient
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1FiniteCandidateSemanticAdmissionExact as Candidate
import DASHI.Mathematics.Complexity.PNotEqualsNPArityTrackedTerminalSemanticAdmissionExact as ArityTerminal
import DASHI.Mathematics.Complexity.PNotEqualsNPArityTerminalDirectDPAuthorityExact as DirectDP
import DASHI.Mathematics.Complexity.PNotEqualsNPRestrictionQuotientDynamicProgrammingExact as DP
import DASHI.Mathematics.Complexity.PNotEqualsNPSelfDiagonalResidualWidthExact as Width
import DASHI.Mathematics.Complexity.PNotEqualsNPBoundedSelfReferenceWellFoundedExact as Q2
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1ExecutedConstructionMachineExact as Executed
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1FiniteCodeClayClosureExact as ClayClosure
import DASHI.Mathematics.Complexity.PNotEqualsNPPartialKleeneTerminationNoGoExact as NoGo

------------------------------------------------------------------------
-- A typed machine whose terminal data are only a finite transition table.
------------------------------------------------------------------------

data DirectDPMachineState
    {rootVariables : Nat}
    (root : SAT.BooleanFormula rootVariables)
    (Work : Set) : Set₁ where
  working :
    Work →
    DirectDPMachineState root Work

  finished :
    Candidate.TransitionTableCandidate root →
    DirectDPMachineState root Work

directDPMachineStep :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    {Work : Set} →
  (Work → DirectDPMachineState root Work) →
  DirectDPMachineState root Work →
  DirectDPMachineState root Work
directDPMachineStep advance (working work) =
  advance work
directDPMachineStep advance (finished candidate) =
  finished candidate

------------------------------------------------------------------------
-- Exact payload measure of the one-node next authority plus persistent
-- self-reference overhead.
------------------------------------------------------------------------

directDPAuthorityPayloadMeasure :
  (state : Q2.BoundedSelfReferenceState) →
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables} →
  (candidate : Candidate.TransitionTableCandidate root) →
  ArityTerminal.ArityTrackedTerminalAdmission candidate →
  Nat
directDPAuthorityPayloadMeasure
    state
    candidate
    admission =
  Size.formulaNodeCount
      (DirectDP.arityTerminalDPAuthority
        candidate
        admission)
  +
  (Q2.programCodeSize state
    + Q2.rebindingOverhead state)

------------------------------------------------------------------------
-- One charged live run.
------------------------------------------------------------------------

record DirectDPChargedConstructionRun
    (state : Q2.BoundedSelfReferenceState) : Set₁ where
  constructor direct-dp-charged-construction-run
  field
    Work :
      Set

    advance :
      Work →
      DirectDPMachineState
        (Bridge.cookToIndexed
          (Q2.currentFormula state))
        Work

    initialWork :
      Work

    candidate :
      Candidate.TransitionTableCandidate
        (Bridge.cookToIndexed
          (Q2.currentFormula state))

    machineStepCount :
      Nat

    machineExecution :
      Executed.Iterates
        (directDPMachineStep advance)
        machineStepCount
        (working initialWork)
        (finished candidate)

    localAdmission :
      ArityTerminal.ArityTrackedTerminalAdmission
        candidate

    machineEvaluationAndNextPayloadStrict :
      (DirectDP.arityTerminalEvaluationCellCount
        candidate
        localAdmission
        + machineStepCount)
      +
      directDPAuthorityPayloadMeasure
        state
        candidate
        localAdmission
      <
      Q2.recursiveMeasure state

open DirectDPChargedConstructionRun public

------------------------------------------------------------------------
-- The strict charge itself proves the next one-node authority state fits the
-- existing resource-budget ceiling.
------------------------------------------------------------------------

directDPNextFitsBudget :
  ∀ {state : Q2.BoundedSelfReferenceState}
    (run : DirectDPChargedConstructionRun state) →
  directDPAuthorityPayloadMeasure
      state
      (candidate run)
      (localAdmission run)
  ≤
  Q2.resourceBudget state
directDPNextFitsBudget {state} run =
  NatP.≤-trans
    payloadBelowCurrent
    (Q2.stateFitsBudget state)
  where
    constructionCost :
      Nat
    constructionCost =
      DirectDP.arityTerminalEvaluationCellCount
        (candidate run)
        (localAdmission run)
      + machineStepCount run

    payload :
      Nat
    payload =
      directDPAuthorityPayloadMeasure
        state
        (candidate run)
        (localAdmission run)

    payloadBelowCharged :
      payload
      ≤
      constructionCost + payload
    payloadBelowCharged =
      NatP.n≤m+n payload constructionCost

    payloadBelowCurrent :
      payload
      ≤
      Q2.recursiveMeasure state
    payloadBelowCurrent =
      NatP.≤-trans
        payloadBelowCharged
        (NatP.<⇒≤
          (machineEvaluationAndNextPayloadStrict run))

------------------------------------------------------------------------
-- Literal next Q2 state.
------------------------------------------------------------------------

directDPNextState :
  ∀ {state : Q2.BoundedSelfReferenceState} →
  DirectDPChargedConstructionRun state →
  Q2.BoundedSelfReferenceState
directDPNextState {state} run =
  Q2.bounded-self-reference-state
    (DirectDP.arityTerminalDPAuthority
      (candidate run)
      (localAdmission run))
    (Q2.programCodeSize state)
    (Q2.rebindingOverhead state)
    (Q2.resourceBudget state)
    (directDPNextFitsBudget run)

directDPNextMeasureExact :
  ∀ {state : Q2.BoundedSelfReferenceState}
    (run : DirectDPChargedConstructionRun state) →
  Q2.recursiveMeasure
      (directDPNextState run)
  ≡
  directDPAuthorityPayloadMeasure
      state
      (candidate run)
      (localAdmission run)
directDPNextMeasureExact run =
  refl

directDPNextStrictlyDecreases :
  ∀ {state : Q2.BoundedSelfReferenceState}
    (run : DirectDPChargedConstructionRun state) →
  Q2.recursiveMeasure
      (directDPNextState run)
  <
  Q2.recursiveMeasure state
directDPNextStrictlyDecreases {state} run =
  NatP.≤-<-trans
    nextBelowCharged
    (machineEvaluationAndNextPayloadStrict run)
  where
    constructionCost :
      Nat
    constructionCost =
      DirectDP.arityTerminalEvaluationCellCount
        (candidate run)
        (localAdmission run)
      + machineStepCount run

    nextBelowCharged :
      Q2.recursiveMeasure
          (directDPNextState run)
      ≤
      constructionCost
        +
      directDPAuthorityPayloadMeasure
        state
        (candidate run)
        (localAdmission run)
    nextBelowCharged
      rewrite directDPNextMeasureExact run =
      NatP.n≤m+n
        (directDPAuthorityPayloadMeasure
          state
          (candidate run)
          (localAdmission run))
        constructionCost

------------------------------------------------------------------------
-- Quotient graph is exactly three cells per state.
------------------------------------------------------------------------

admittedGraphCellCountIsTriple :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (candidate : Candidate.TransitionTableCandidate root)
    (admission :
      ArityTerminal.ArityTrackedTerminalAdmission candidate) →
  Quotient.quotientGraphCellCount
      (DirectDP.admittedQuotient candidate admission)
  ≡
  Width.triple
    (Candidate.stateCount candidate)
admittedGraphCellCountIsTriple candidate admission
    rewrite
      Width.twoTimes
        (Candidate.stateCount candidate) =
  refl

tripleStateCountBelowEvaluationCellCount :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (candidate : Candidate.TransitionTableCandidate root)
    (admission :
      ArityTerminal.ArityTrackedTerminalAdmission candidate) →
  Width.triple
      (Candidate.stateCount candidate)
  ≤
  DirectDP.arityTerminalEvaluationCellCount
      candidate
      admission
tripleStateCountBelowEvaluationCellCount
    candidate
    admission
    rewrite
      sym
        (admittedGraphCellCountIsTriple
          candidate
          admission) =
  NatP.m≤m+n
    (Quotient.quotientGraphCellCount
      (DirectDP.admittedQuotient candidate admission))
    (DP.quotientDynamicTableCellCount
      (DirectDP.admittedQuotient candidate admission))

------------------------------------------------------------------------
-- One-layer semantic width already charges the graph.  An all-layer stack is
-- stronger, but not required for the exponential equality falsification.
------------------------------------------------------------------------

directDPResidualWidthBelowStateCount :
  ∀ {state : Q2.BoundedSelfReferenceState}
    {remaining width : Nat}
    (run : DirectDPChargedConstructionRun state) →
  Width.ResidualWidthWitness
    {root =
      Bridge.cookToIndexed
        (Q2.currentFormula state)}
    remaining
    width →
  width
  ≤
  Candidate.stateCount
    (candidate run)
directDPResidualWidthBelowStateCount run witness =
  Width.residualWidthBelowArityAdmittedCandidateStateCount
    (localAdmission run)
    witness

directDPTripleResidualWidthBelowEvaluation :
  ∀ {state : Q2.BoundedSelfReferenceState}
    {remaining width : Nat}
    (run : DirectDPChargedConstructionRun state) →
  Width.ResidualWidthWitness
    {root =
      Bridge.cookToIndexed
        (Q2.currentFormula state)}
    remaining
    width →
  Width.triple width
  ≤
  DirectDP.arityTerminalEvaluationCellCount
    (candidate run)
    (localAdmission run)
directDPTripleResidualWidthBelowEvaluation
    run
    witness =
  NatP.≤-trans
    (Width.tripleMonotone
      (directDPResidualWidthBelowStateCount
        run
        witness))
    (tripleStateCountBelowEvaluationCellCount
      (candidate run)
      (localAdmission run))

directDPTripleResidualWidthStrictlyBelowCurrentMeasure :
  ∀ {state : Q2.BoundedSelfReferenceState}
    {remaining width : Nat}
    (run : DirectDPChargedConstructionRun state) →
  Width.ResidualWidthWitness
    {root =
      Bridge.cookToIndexed
        (Q2.currentFormula state)}
    remaining
    width →
  Width.triple width
  <
  Q2.recursiveMeasure state
directDPTripleResidualWidthStrictlyBelowCurrentMeasure
    {state}
    run
    witness =
  NatP.≤-<-trans
    widthBelowWholeCharge
    (machineEvaluationAndNextPayloadStrict run)
  where
    evaluation :
      Nat
    evaluation =
      DirectDP.arityTerminalEvaluationCellCount
        (candidate run)
        (localAdmission run)

    machine :
      Nat
    machine =
      machineStepCount run

    payload :
      Nat
    payload =
      directDPAuthorityPayloadMeasure
        state
        (candidate run)
        (localAdmission run)

    widthBelowEvaluation :
      Width.triple _
      ≤
      evaluation
    widthBelowEvaluation =
      directDPTripleResidualWidthBelowEvaluation
        run
        witness

    widthBelowWholeCharge :
      Width.triple _
      ≤
      (evaluation + machine) + payload
    widthBelowWholeCharge =
      NatP.≤-trans
        widthBelowEvaluation
        (NatP.≤-trans
          (NatP.m≤m+n evaluation machine)
          (NatP.m≤m+n
            (evaluation + machine)
            payload))

directDPSingleLayerHighWidthBlocksRun :
  ∀ {state : Q2.BoundedSelfReferenceState}
    {remaining width : Nat} →
  Width.ResidualWidthWitness
    {root =
      Bridge.cookToIndexed
        (Q2.currentFormula state)}
    remaining
    width →
  Q2.recursiveMeasure state
  ≤
  Width.triple width →
  DirectDPChargedConstructionRun state →
  ⊥
directDPSingleLayerHighWidthBlocksRun
    witness
    measureBelowWidth
    run =
  NatP.<⇒≱
    (directDPTripleResidualWidthStrictlyBelowCurrentMeasure
      run
      witness)
    measureBelowWidth

------------------------------------------------------------------------
-- Semantic width therefore charges directly into the represented evaluator.
------------------------------------------------------------------------

directDPLayeredWidthBelowStateCount :
  ∀ {state : Q2.BoundedSelfReferenceState}
    {next total : Nat}
    (run : DirectDPChargedConstructionRun state) →
  Width.ResidualWidthStack
    {root =
      Bridge.cookToIndexed
        (Q2.currentFormula state)}
    next
    total →
  total
  ≤
  Candidate.stateCount
    (candidate run)
directDPLayeredWidthBelowStateCount run stack =
  Width.layeredResidualWidthSumBelowCandidateStateCount
    (localAdmission run)
    stack

directDPTripleLayeredWidthBelowEvaluation :
  ∀ {state : Q2.BoundedSelfReferenceState}
    {next total : Nat}
    (run : DirectDPChargedConstructionRun state) →
  Width.ResidualWidthStack
    {root =
      Bridge.cookToIndexed
        (Q2.currentFormula state)}
    next
    total →
  Width.triple total
  ≤
  DirectDP.arityTerminalEvaluationCellCount
    (candidate run)
    (localAdmission run)
directDPTripleLayeredWidthBelowEvaluation
    run
    stack =
  NatP.≤-trans
    (Width.tripleMonotone
      (directDPLayeredWidthBelowStateCount
        run
        stack))
    (tripleStateCountBelowEvaluationCellCount
      (candidate run)
      (localAdmission run))

directDPTripleLayeredWidthStrictlyBelowCurrentMeasure :
  ∀ {state : Q2.BoundedSelfReferenceState}
    {next total : Nat}
    (run : DirectDPChargedConstructionRun state) →
  Width.ResidualWidthStack
    {root =
      Bridge.cookToIndexed
        (Q2.currentFormula state)}
    next
    total →
  Width.triple total
  <
  Q2.recursiveMeasure state
directDPTripleLayeredWidthStrictlyBelowCurrentMeasure
    {state}
    run
    stack =
  NatP.≤-<-trans
    widthBelowWholeCharge
    (machineEvaluationAndNextPayloadStrict run)
  where
    evaluation :
      Nat
    evaluation =
      DirectDP.arityTerminalEvaluationCellCount
        (candidate run)
        (localAdmission run)

    machine :
      Nat
    machine =
      machineStepCount run

    payload :
      Nat
    payload =
      directDPAuthorityPayloadMeasure
        state
        (candidate run)
        (localAdmission run)

    widthBelowEvaluation :
      Width.triple _
      ≤
      evaluation
    widthBelowEvaluation =
      directDPTripleLayeredWidthBelowEvaluation
        run
        stack

    widthBelowConstruction :
      Width.triple _
      ≤
      evaluation + machine
    widthBelowConstruction =
      NatP.≤-trans
        widthBelowEvaluation
        (NatP.m≤m+n evaluation machine)

    widthBelowWholeCharge :
      Width.triple _
      ≤
      (evaluation + machine) + payload
    widthBelowWholeCharge =
      NatP.≤-trans
        widthBelowConstruction
        (NatP.m≤m+n
          (evaluation + machine)
          payload)

directDPHighWidthBlocksRun :
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
  DirectDPChargedConstructionRun state →
  ⊥
directDPHighWidthBlocksRun
    stack
    measureBelowWidth
    run =
  NatP.<⇒≱
    (directDPTripleLayeredWidthStrictlyBelowCurrentMeasure
      run
      stack)
    measureBelowWidth

------------------------------------------------------------------------
-- Total direct-DP constructor and Q2 step system.
------------------------------------------------------------------------

DirectDPChargedStateConstructor : Set₁
DirectDPChargedStateConstructor =
  (state : Q2.BoundedSelfReferenceState) →
  Maybe (DirectDPChargedConstructionRun state)

directDPNext :
  DirectDPChargedStateConstructor →
  Q2.BoundedSelfReferenceState →
  Maybe Q2.BoundedSelfReferenceState
directDPNext constructor state
    with constructor state
... | nothing =
  nothing
... | just run =
  just (directDPNextState run)

justInjective :
  ∀ {A : Set} {left right : A} →
  just left ≡ just right →
  left ≡ right
justInjective refl =
  refl

directDPNextSystemStrict :
  (constructor : DirectDPChargedStateConstructor) →
  (state nextState : Q2.BoundedSelfReferenceState) →
  directDPNext constructor state
  ≡
  just nextState →
  Q2.recursiveMeasure nextState
  <
  Q2.recursiveMeasure state
directDPNextSystemStrict
    constructor
    state
    nextState
    equation
    with constructor state
... | nothing =
  impossible equation
  where
    impossible :
      nothing ≡ just nextState →
      Q2.recursiveMeasure nextState
      <
      Q2.recursiveMeasure state
    impossible ()
... | just run =
  transport
    (justInjective equation)
    (directDPNextStrictlyDecreases run)
  where
    transport :
      ∀ {left right : Q2.BoundedSelfReferenceState} →
      left ≡ right →
      Q2.recursiveMeasure left
        <
      Q2.recursiveMeasure state →
      Q2.recursiveMeasure right
        <
      Q2.recursiveMeasure state
    transport refl proof =
      proof

directDPConstructorToQ2StepSystem :
  DirectDPChargedStateConstructor →
  Q2.BoundedSelfReferenceStepSystem
directDPConstructorToQ2StepSystem constructor =
  Q2.bounded-self-reference-step-system
    (directDPNext constructor)
    (directDPNextSystemStrict constructor)

------------------------------------------------------------------------
-- Existing finite-code fixed-point / Clay contradiction compiler is reusable
-- unchanged on the direct-DP step system.
------------------------------------------------------------------------

directDPRecurrenceFiniteCodeContradictsSATInP :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    (satP : PR.InP cost Clay.SATLanguage)
    (constructor : DirectDPChargedStateConstructor)
    (initial : Q2.BoundedSelfReferenceState) →
  ClayClosure.Q1OppositeSATTerminalSemantics
    (NoGo.satPCandidate satP)
    (directDPConstructorToQ2StepSystem constructor)
    initial →
  ⊥
directDPRecurrenceFiniteCodeContradictsSATInP
    satP
    constructor
    initial
    semantics =
  ClayClosure.q1FiniteCodeContradictsSATInP
    satP
    (directDPConstructorToQ2StepSystem constructor)
    initial
    semantics

------------------------------------------------------------------------
-- FRONTIER CONSEQUENCE
--
-- This is now the preferred P carrier.
--
-- Removed:
--   raw strict restriction representatives
--   per-state rewrite-to-constant programs
--   closed representative chains
--
-- Retained:
--   finite transition table
--   typed construction execution
--   local arity/terminal correctness
--   exact quotient-DP semantics
--   literal graph/table resource accounting
--   whole-state self-reference descent
--
-- The next experiment is genuinely sharp:
--
--   either build this object for the actual live self-instantiation roots,
--   or exhibit a residual-width stack whose unavoidable evaluator graph alone
--   exceeds the recursive measure.
------------------------------------------------------------------------
