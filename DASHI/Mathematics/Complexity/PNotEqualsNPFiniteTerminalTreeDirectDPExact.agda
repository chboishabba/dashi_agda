module DASHI.Mathematics.Complexity.PNotEqualsNPFiniteTerminalTreeDirectDPExact where

------------------------------------------------------------------------
-- FINITE TERMINAL TREE -> LIVE DIRECT-DP CHARGED RECURRENCE
--
-- The strongest live recurrence on master is DirectDPChargedConstructionRun.
-- Its semantic input is an ArityTrackedTerminalAdmission, whose terminal part
-- is still a global theorem over every zero-variable RestrictionDerivation.
--
-- FiniteTerminalTreeAdmissionExact removes that global premise. This owner
-- puts the finite-tree certificate on the ACTUAL direct-DP charged path.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (_≤_; _<_)

import DASHI.Mathematics.Complexity.BooleanFormulaSATSelfReductionExact as SAT
import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.PNotEqualsNPClayCoreExact as Clay
import DASHI.Mathematics.Complexity.PNotEqualsNPCookIndexedFormulaBridgeExact as Bridge
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1FiniteCandidateSemanticAdmissionExact as Candidate
import DASHI.Mathematics.Complexity.PNotEqualsNPFiniteTerminalTreeAdmissionExact as Tree
import DASHI.Mathematics.Complexity.PNotEqualsNPLocalArityTerminalAdmissionExact as Local
import DASHI.Mathematics.Complexity.PNotEqualsNPArityTrackedTerminalSemanticAdmissionExact as ArityTerminal
import DASHI.Mathematics.Complexity.PNotEqualsNPArityTerminalDirectDPAuthorityExact as Authority
import DASHI.Mathematics.Complexity.PNotEqualsNPDirectDPChargedRecurrenceExact as DirectDP
import DASHI.Mathematics.Complexity.PNotEqualsNPBoundedSelfReferenceWellFoundedExact as Q2
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1ExecutedConstructionMachineExact as Executed
import DASHI.Mathematics.Complexity.PNotEqualsNPSelfDiagonalResidualWidthExact as Width
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1FiniteCodeClayClosureExact as ClayClosure
import DASHI.Mathematics.Complexity.PNotEqualsNPPartialKleeneTerminationNoGoExact as NoGo

------------------------------------------------------------------------
-- Derived admission used by every existing direct-DP theorem.
------------------------------------------------------------------------

treeAdmissionToArityAdmission :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    {candidate : Candidate.TransitionTableCandidate root} →
  Tree.TreeLocalArityTerminalAdmission candidate →
  ArityTerminal.ArityTrackedTerminalAdmission candidate
treeAdmissionToArityAdmission admission =
  Local.localBuildsArityTrackedTerminalAdmission
    (Tree.treeLocalBuildsLocalAdmission admission)

------------------------------------------------------------------------
-- Exact tree-certified direct-DP run.
------------------------------------------------------------------------

record TreeDirectDPChargedConstructionRun
    (state : Q2.BoundedSelfReferenceState) : Set₁ where
  constructor tree-direct-dp-charged-construction-run
  field
    Work : Set

    advance :
      Work →
      DirectDP.DirectDPMachineState
        (Bridge.cookToIndexed
          (Q2.currentFormula state))
        Work

    initialWork : Work

    candidate :
      Candidate.TransitionTableCandidate
        (Bridge.cookToIndexed
          (Q2.currentFormula state))

    machineStepCount : Nat

    machineExecution :
      Executed.Iterates
        (DirectDP.directDPMachineStep advance)
        machineStepCount
        (DirectDP.working initialWork)
        (DirectDP.finished candidate)

    treeAdmission :
      Tree.TreeLocalArityTerminalAdmission candidate

    machineEvaluationAndNextPayloadStrict :
      (Authority.arityTerminalEvaluationCellCount
        candidate
        (treeAdmissionToArityAdmission treeAdmission)
        + machineStepCount)
      +
      DirectDP.directDPAuthorityPayloadMeasure
        state
        candidate
        (treeAdmissionToArityAdmission treeAdmission)
      <
      Q2.recursiveMeasure state

open TreeDirectDPChargedConstructionRun public

------------------------------------------------------------------------
-- Forget only the finite-tree presentation; all semantics are derived.
------------------------------------------------------------------------

treeRunToDirectDPRun :
  ∀ {state : Q2.BoundedSelfReferenceState} →
  TreeDirectDPChargedConstructionRun state →
  DirectDP.DirectDPChargedConstructionRun state
treeRunToDirectDPRun run =
  DirectDP.direct-dp-charged-construction-run
    (Work run)
    (advance run)
    (initialWork run)
    (candidate run)
    (machineStepCount run)
    (machineExecution run)
    (treeAdmissionToArityAdmission
      (treeAdmission run))
    (machineEvaluationAndNextPayloadStrict run)

------------------------------------------------------------------------
-- Total constructor and Q2 system.
------------------------------------------------------------------------

TreeDirectDPChargedStateConstructor : Set₁
TreeDirectDPChargedStateConstructor =
  (state : Q2.BoundedSelfReferenceState) →
  Maybe (TreeDirectDPChargedConstructionRun state)

treeConstructorToDirectDP :
  TreeDirectDPChargedStateConstructor →
  DirectDP.DirectDPChargedStateConstructor
treeConstructorToDirectDP constructor state
    with constructor state
... | nothing = nothing
... | just run = just (treeRunToDirectDPRun run)

treeConstructorToQ2StepSystem :
  TreeDirectDPChargedStateConstructor →
  Q2.BoundedSelfReferenceStepSystem
treeConstructorToQ2StepSystem constructor =
  DirectDP.directDPConstructorToQ2StepSystem
    (treeConstructorToDirectDP constructor)

------------------------------------------------------------------------
-- Existing quantitative obstruction transported to the tree-certified path.
------------------------------------------------------------------------

treeDirectDPHighWidthForcesStop :
  ∀ {state : Q2.BoundedSelfReferenceState}
    {remaining width : Nat}
    (witness :
      Width.ResidualWidthWitness
        {root =
          Bridge.cookToIndexed
            (Q2.currentFormula state)}
        remaining
        width)
    (measureBelowWidth :
      Q2.recursiveMeasure state
      ≤
      Width.triple width)
    (constructor : TreeDirectDPChargedStateConstructor) →
  constructor state ≡ nothing
treeDirectDPHighWidthForcesStop
    witness
    measureBelowWidth
    constructor
    with constructor state
... | nothing = refl
... | just run =
  ⊥-elim
    (DirectDP.directDPSingleLayerHighWidthBlocksRun
      witness
      measureBelowWidth
      (treeRunToDirectDPRun run))

------------------------------------------------------------------------
-- Clay-facing compatibility theorem.
--
-- This does NOT manufacture opposite-SAT semantics; master correctly proves
-- that premise is already a concrete SAT decision failure in disguise.
------------------------------------------------------------------------

treeDirectDPRecurrenceContradictsSATInP :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    (satP : PR.InP cost Clay.SATLanguage)
    (constructor : TreeDirectDPChargedStateConstructor)
    (initial : Q2.BoundedSelfReferenceState) →
  ClayClosure.Q1OppositeSATTerminalSemantics
    (NoGo.satPCandidate satP)
    (treeConstructorToQ2StepSystem constructor)
    initial →
  ⊥
treeDirectDPRecurrenceContradictsSATInP
    satP
    constructor
    initial
    semantics =
  ClayClosure.q1FiniteCodeContradictsSATInP
    satP
    (treeConstructorToQ2StepSystem constructor)
    initial
    semantics

------------------------------------------------------------------------
-- FRONTIER CONSEQUENCE
--
-- Global terminalLabelCorrect is no longer primitive on the live direct-DP
-- route. Terminal semantic authority is a finite proof tree following the
-- exact emitted transition table.
--
-- The remaining non-circular Clay debt is NOT terminal semantics. It is the
-- candidate-coupled progress law identified on master:
--
--   candidate/self-code -> same-object live root -> constructor(root) != nothing.
------------------------------------------------------------------------
