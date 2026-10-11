module DASHI.Mathematics.Complexity.PNotEqualsNPRepairedFiniteCandidateAdmissionExact where

------------------------------------------------------------------------
-- REPAIRED FINITE Q1 CANDIDATE + ADMISSION + MACHINE PATH
--
-- The old FiniteQ1Candidate is uninhabited because it requires a raw Shannon
-- restriction to be strictly smaller than the root by Cook node count.
--
-- This owner replaces that empty carrier end-to-end.
--
-- Machine-emittable DATA:
--   * finite transition table;
--   * root-nontrivial size receipt;
--   * for each state, an actually reachable raw restriction;
--   * an answer-blind RewriteProgram normalizing that raw formula to a literal
--     constant.
--
-- Separate admission:
--   * finite terminal verification tree + local arity laws.
--
-- Admission derives semantic congruence.  Only then do the normalized literal
-- constants become the strict semantic representatives consumed by existing
-- closed-Q1/Q2 machinery.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Fin.Base using (Fin)
open import Data.List.Base using (length)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (_<_)
open import Data.Product using (Σ; _,_)

import DASHI.Mathematics.Complexity.BooleanFormulaSATSelfReductionExact as SAT
import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PNotEqualsNPCookIndexedFormulaBridgeExact as Bridge
import DASHI.Mathematics.Complexity.PNotEqualsNPProgramDescriptionFormulaEmbeddingExact as Size
import DASHI.Mathematics.Complexity.PNotEqualsNPSelfDiagonalRestrictionFamilyExact as Family
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1FiniteCandidateSemanticAdmissionExact as Candidate
import DASHI.Mathematics.Complexity.PNotEqualsNPFiniteTerminalTreeAdmissionExact as Tree
import DASHI.Mathematics.Complexity.PNotEqualsNPLocalArityTerminalAdmissionExact as Local
import DASHI.Mathematics.Complexity.PNotEqualsNPRewrittenRepresentativeCandidateExact as Rewritten
import DASHI.Mathematics.Complexity.PNotEqualsNPAnswerBlindStructuralRewriteMachineExact as Rewrite
import DASHI.Mathematics.Complexity.PNotEqualsNPRewriteGeneratedQ1DiscoveryExact as RewriteGenerated
import DASHI.Mathematics.Complexity.PNotEqualsNPSelfReferenceAllOverheadBudgetExact as Q1
import DASHI.Mathematics.Complexity.PNotEqualsNPBoundedSelfReferenceWellFoundedExact as Q2
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1ReachableStateRecurrenceExact as Recurrence
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1ExecutedConstructionMachineExact as Executed
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1OperationalConstructionCostExact as Operational
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1ConstructionChargedRecurrenceExact as Charged
import DASHI.Mathematics.Complexity.PNotEqualsNPResourceClosingRestrictionQuotientExact as Quotient

------------------------------------------------------------------------
-- One machine-emittable normalized state.
------------------------------------------------------------------------

record FiniteNormalizedState
    {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (transition : Candidate.TransitionTableCandidate root)
    (state : Fin (Candidate.stateCount transition)) : Set₁ where
  constructor finite-normalized-state
  field
    currentVariables : Nat
    rawFormula : SAT.BooleanFormula currentVariables

    rawDerivation :
      Family.RestrictionDerivation root rawFormula

    rawSelectsState :
      Candidate.candidateSelect transition rawDerivation
      ≡
      state

    normalization :
      Rewrite.RewriteProgram
        (Bridge.indexedToCook rawFormula)

open FiniteNormalizedState public

------------------------------------------------------------------------
-- Pure finite repaired candidate: NO semantic-congruence theorem field.
------------------------------------------------------------------------

record RepairedFiniteQ1Candidate
    {rootVariables : Nat}
    (root : SAT.BooleanFormula rootVariables) : Set₁ where
  constructor repaired-finite-q1-candidate
  field
    transitionCandidate :
      Candidate.TransitionTableCandidate root

    rootNontrivial :
      suc zero
      <
      Size.formulaNodeCount
        (Bridge.indexedToCook root)

    normalizedState :
      (state : Fin (Candidate.stateCount transitionCandidate)) →
      FiniteNormalizedState transitionCandidate state

open RepairedFiniteQ1Candidate public

------------------------------------------------------------------------
-- Semantic admission converts finite data to the repaired strict carrier.
------------------------------------------------------------------------

admitRepairedFiniteCandidate :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (candidate : RepairedFiniteQ1Candidate root) →
  Candidate.GeneratedSemanticCongruence
    (transitionCandidate candidate) →
  Rewritten.RewrittenRepresentativeCandidate root
admitRepairedFiniteCandidate candidate semanticCongruence =
  Rewritten.rewritten-representative-candidate
    generated
    (rootNontrivial candidate)
    admittedState
  where
    transition :
      Candidate.TransitionTableCandidate root
    transition =
      transitionCandidate candidate

    generated =
      Candidate.admitTransitionTableCandidate
        transition
        semanticCongruence

    admittedState :
      (state : Fin (Candidate.stateCount transition)) →
      Rewritten.NormalizedReachableState generated state
    admittedState state =
      Rewritten.normalized-reachable-state
        (FiniteNormalizedState.currentVariables source)
        (FiniteNormalizedState.rawFormula source)
        (FiniteNormalizedState.rawDerivation source)
        (FiniteNormalizedState.rawSelectsState source)
        (FiniteNormalizedState.normalization source)
      where
        source :
          FiniteNormalizedState transition state
        source =
          normalizedState candidate state

------------------------------------------------------------------------
-- Terminal-tree admission derives semantic congruence and then strict closure.
------------------------------------------------------------------------

admitTreeRepairedCandidate :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (candidate : RepairedFiniteQ1Candidate root) →
  Tree.TreeLocalArityTerminalAdmission
    (transitionCandidate candidate) →
  Rewritten.RewrittenRepresentativeCandidate root
admitTreeRepairedCandidate candidate admission =
  admitRepairedFiniteCandidate
    candidate
    (Local.localArityTerminalBuildsSemanticCongruence
      (Tree.treeLocalBuildsLocalAdmission admission))

repairedClosedQuotient :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (candidate : RepairedFiniteQ1Candidate root)
    (admission :
      Tree.TreeLocalArityTerminalAdmission
        (transitionCandidate candidate)) →
  RewriteGenerated.RewriteGeneratedClosedRepresentativeQuotient root
repairedClosedQuotient candidate admission =
  Rewritten.toRewriteGeneratedClosedRepresentativeQuotient
    (admitTreeRepairedCandidate candidate admission)

------------------------------------------------------------------------
-- State-specific admitted witness.
------------------------------------------------------------------------

record AdmittedRepairedQ1StateWitness
    (state : Q2.BoundedSelfReferenceState) : Set₁ where
  constructor admitted-repaired-q1-state-witness
  field
    candidate :
      RepairedFiniteQ1Candidate
        (Bridge.cookToIndexed
          (Q2.currentFormula state))

    treeAdmission :
      Tree.TreeLocalArityTerminalAdmission
        (transitionCandidate candidate)

    allOverheadFits :
      Q1.ClosedQuotientAllOverheadFits
        (RewriteGenerated.toClosedStrictRepresentativeQuotient
          (repairedClosedQuotient
            candidate
            treeAdmission))
        (Recurrence.stateOverhead state)

open AdmittedRepairedQ1StateWitness public

admittedRepairedToRewriteGeneratedWitness :
  ∀ {state : Q2.BoundedSelfReferenceState} →
  AdmittedRepairedQ1StateWitness state →
  RewriteGenerated.RewriteGeneratedQ1StateWitness state
admittedRepairedToRewriteGeneratedWitness admitted =
  repairedClosedQuotient
    (candidate admitted)
    (treeAdmission admitted)
  ,
  allOverheadFits admitted

admittedRepairedToLegacyWitness :
  ∀ {state : Q2.BoundedSelfReferenceState} →
  AdmittedRepairedQ1StateWitness state →
  Recurrence.Q1StateWitness state
admittedRepairedToLegacyWitness admitted =
  RewriteGenerated.rewriteGeneratedWitnessToLegacy
    (admittedRepairedToRewriteGeneratedWitness admitted)

------------------------------------------------------------------------
-- Machine execution emits only the repaired finite data.
------------------------------------------------------------------------

data RepairedCandidateMachineState
    {rootVariables : Nat}
    (root : SAT.BooleanFormula rootVariables)
    (Work : Set) : Set₁ where
  working :
    Work →
    RepairedCandidateMachineState root Work

  finished :
    RepairedFiniteQ1Candidate root →
    RepairedCandidateMachineState root Work

repairedCandidateMachineStep :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    {Work : Set} →
  (Work → RepairedCandidateMachineState root Work) →
  RepairedCandidateMachineState root Work →
  RepairedCandidateMachineState root Work
repairedCandidateMachineStep advance (working work) =
  advance work
repairedCandidateMachineStep advance (finished candidate) =
  finished candidate

record RepairedFiniteCandidateConstructionRun
    (state : Q2.BoundedSelfReferenceState) : Set₁ where
  constructor repaired-finite-candidate-construction-run
  field
    Work : Set

    advance :
      Work →
      RepairedCandidateMachineState
        (Bridge.cookToIndexed
          (Q2.currentFormula state))
        Work

    initialWork : Work

    finiteCandidate :
      RepairedFiniteQ1Candidate
        (Bridge.cookToIndexed
          (Q2.currentFormula state))

    machineStepCount : Nat

    machineExecution :
      Executed.Iterates
        (repairedCandidateMachineStep advance)
        machineStepCount
        (working initialWork)
        (finished finiteCandidate)

open RepairedFiniteCandidateConstructionRun public

------------------------------------------------------------------------
-- Admission stays outside the machine and is indexed by the exact final data.
------------------------------------------------------------------------

record TreeAdmittedRepairedConstructionRun
    (state : Q2.BoundedSelfReferenceState) : Set₁ where
  constructor tree-admitted-repaired-construction-run
  field
    construction :
      RepairedFiniteCandidateConstructionRun state

    treeAdmission :
      Tree.TreeLocalArityTerminalAdmission
        (transitionCandidate
          (finiteCandidate construction))

    allOverheadFits :
      Q1.ClosedQuotientAllOverheadFits
        (RewriteGenerated.toClosedStrictRepresentativeQuotient
          (repairedClosedQuotient
            (finiteCandidate construction)
            treeAdmission))
        (Recurrence.stateOverhead state)

    machineConstructionAndNextStrict :
      (Operational.q1WitnessGraphCellCount
        (admittedRepairedToLegacyWitness
          (admitted-repaired-q1-state-witness
            (finiteCandidate construction)
            treeAdmission
            allOverheadFits))
        + machineStepCount construction)
      +
      Q2.recursiveMeasure
        (Charged.q1WitnessNextState
          state
          (admittedRepairedToLegacyWitness
            (admitted-repaired-q1-state-witness
              (finiteCandidate construction)
              treeAdmission
              allOverheadFits)))
      <
      Q2.recursiveMeasure state

open TreeAdmittedRepairedConstructionRun public

admittedRunWitness :
  ∀ {state : Q2.BoundedSelfReferenceState} →
  TreeAdmittedRepairedConstructionRun state →
  AdmittedRepairedQ1StateWitness state
admittedRunWitness run =
  admitted-repaired-q1-state-witness
    (finiteCandidate (construction run))
    (treeAdmission run)
    (allOverheadFits run)

------------------------------------------------------------------------
-- Compatibility compiler to the existing operational Q1 recurrence.
------------------------------------------------------------------------

treeAdmittedRepairedRunToOperational :
  ∀ {state : Q2.BoundedSelfReferenceState} →
  TreeAdmittedRepairedConstructionRun state →
  Operational.OperationalQ1ConstructionRun state
treeAdmittedRepairedRunToOperational {state} run =
  record
    { Operational.q1Witness = witness
    ; Operational.emittedFalseTarget =
        λ stateIndex →
          Quotient.step
            (Operational.q1WitnessQuotient witness)
            stateIndex
            Agda.Builtin.Bool.false
    ; Operational.emittedTrueTarget =
        λ stateIndex →
          Quotient.step
            (Operational.q1WitnessQuotient witness)
            stateIndex
            Agda.Builtin.Bool.true
    ; Operational.emittedFalseTargetExact = λ stateIndex → refl
    ; Operational.emittedTrueTargetExact = λ stateIndex → refl
    ; Operational.auxiliaryTrace =
        Executed.unitTrace
          (machineStepCount (construction run))
    ; Operational.operationalAndNextStrict = strict
    }
  where
    witness : Recurrence.Q1StateWitness state
    witness =
      admittedRepairedToLegacyWitness
        (admittedRunWitness run)

    strict :
      (Operational.q1WitnessGraphCellCount witness
        +
        length
          (Executed.unitTrace
            (machineStepCount (construction run))))
      +
      Q2.recursiveMeasure
        (Charged.q1WitnessNextState state witness)
      <
      Q2.recursiveMeasure state
    strict
      rewrite
        Executed.unitTraceLengthExact
          (machineStepCount (construction run)) =
      machineConstructionAndNextStrict run

TreeAdmittedRepairedStateConstructor : Set₁
TreeAdmittedRepairedStateConstructor =
  (state : Q2.BoundedSelfReferenceState) →
  Maybe (TreeAdmittedRepairedConstructionRun state)

treeAdmittedRepairedConstructorToOperational :
  TreeAdmittedRepairedStateConstructor →
  Operational.OperationalQ1StateConstructor
treeAdmittedRepairedConstructorToOperational constructor state
    with constructor state
... | nothing = nothing
... | just run = just (treeAdmittedRepairedRunToOperational run)

treeAdmittedRepairedConstructorToQ2StepSystem :
  TreeAdmittedRepairedStateConstructor →
  Q2.BoundedSelfReferenceStepSystem
treeAdmittedRepairedConstructorToQ2StepSystem constructor =
  Operational.operationalConstructorToQ2StepSystem
    (treeAdmittedRepairedConstructorToOperational constructor)

------------------------------------------------------------------------
-- FRONTIER CONSEQUENCE
--
-- The live machine path no longer depends on the impossible old
-- FiniteQ1Candidate.  Strictness sits on normalized literal constants, while
-- raw restrictions retain only provenance/state-membership authority.
------------------------------------------------------------------------
