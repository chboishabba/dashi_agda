module DASHI.Mathematics.Complexity.PNotEqualsNPQ1FiniteCandidateSemanticAdmissionExact where

------------------------------------------------------------------------
-- Q1 FINITE CANDIDATE / SEMANTIC ADMISSION FIREWALL
--
-- The construction machine must emit DATA, not the theorem that the data is a
-- correct semantic quotient.
--
-- Machine-emittable candidate:
--   * stateCount
--   * rootState
--   * Boolean transition table
--   * one actually reachable representative node per state
--   * strict size receipt for that representative
--   * restricted structural RewriteProgram to a literal constant
--
-- NOT machine output:
--   * generated-state semantic congruence;
--   * all-overhead Q1 fit.
--
-- Those are separately checked admission obligations.  Only after admission is
-- the finite candidate compiled to the existing reachable/rewrite-generated Q1
-- witness and then to Q2.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
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
import DASHI.Mathematics.Complexity.PNotEqualsNPTransitionGeneratedRestrictionQuotientExact as Generated
import DASHI.Mathematics.Complexity.PNotEqualsNPResourceClosingRestrictionQuotientExact as Quotient
import DASHI.Mathematics.Complexity.PNotEqualsNPAnswerBlindStructuralRewriteMachineExact as Rewrite
import DASHI.Mathematics.Complexity.PNotEqualsNPReachableRewriteGeneratedQ1Exact as Reachable
import DASHI.Mathematics.Complexity.PNotEqualsNPRewriteGeneratedQ1DiscoveryExact as RewriteGenerated
import DASHI.Mathematics.Complexity.PNotEqualsNPSelfReferenceAllOverheadBudgetExact as Q1
import DASHI.Mathematics.Complexity.PNotEqualsNPBoundedSelfReferenceWellFoundedExact as Q2
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1ReachableStateRecurrenceExact as Recurrence
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1ExecutedConstructionMachineExact as Executed
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1OperationalConstructionCostExact as Operational
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1ConstructionChargedRecurrenceExact as Charged

------------------------------------------------------------------------
-- Pure finite transition-table candidate.  No semantic theorem field.
------------------------------------------------------------------------

record TransitionTableCandidate
    {rootVariables : Nat}
    (root : SAT.BooleanFormula rootVariables) : Set where
  constructor transition-table-candidate
  field
    stateCount : Nat
    rootState : Fin stateCount
    step : Fin stateCount → Bool → Fin stateCount

open TransitionTableCandidate public

candidateSelect :
  ∀ {rootVariables currentVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (candidate : TransitionTableCandidate root)
    {current : SAT.BooleanFormula currentVariables} →
  Family.RestrictionDerivation root current →
  Fin (stateCount candidate)
candidateSelect candidate =
  Generated.generatedSelect
    (rootState candidate)
    (step candidate)

------------------------------------------------------------------------
-- Semantic admission is a theorem ABOUT the candidate.
------------------------------------------------------------------------

GeneratedSemanticCongruence :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables} →
  TransitionTableCandidate root →
  Set₁
GeneratedSemanticCongruence {root = root} candidate =
  ∀ {leftVariables rightVariables : Nat}
    {left : SAT.BooleanFormula leftVariables}
    {right : SAT.BooleanFormula rightVariables}
    (leftDerivation :
      Family.RestrictionDerivation root left)
    (rightDerivation :
      Family.RestrictionDerivation root right) →
  candidateSelect candidate leftDerivation
  ≡
  candidateSelect candidate rightDerivation →
  Quotient.SatisfiabilityEquivalent left right

admitTransitionTableCandidate :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (candidate : TransitionTableCandidate root) →
  GeneratedSemanticCongruence candidate →
  Generated.TransitionGeneratedRestrictionQuotient root
admitTransitionTableCandidate candidate congruence =
  Generated.transition-generated-restriction-quotient
    (stateCount candidate)
    (rootState candidate)
    (step candidate)
    congruence

------------------------------------------------------------------------
-- Reachable representative DATA.  Still no semantic equivalence proof.
------------------------------------------------------------------------

record CandidateStateRepresentative
    {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (candidate : TransitionTableCandidate root)
    (state : Fin (stateCount candidate)) : Set₁ where
  constructor candidate-state-representative
  field
    currentVariables : Nat
    formula : SAT.BooleanFormula currentVariables

    derivation :
      Family.RestrictionDerivation root formula

    selectsState :
      candidateSelect candidate derivation
      ≡
      state

    strictlySmallerThanRoot :
      Size.formulaNodeCount
        (Bridge.indexedToCook formula)
      <
      Size.formulaNodeCount
        (Bridge.indexedToCook root)

    rewriteProgram :
      Rewrite.RewriteProgram
        (Bridge.indexedToCook formula)

open CandidateStateRepresentative public

record FiniteQ1Candidate
    {rootVariables : Nat}
    (root : SAT.BooleanFormula rootVariables) : Set₁ where
  constructor finite-q1-candidate
  field
    transitionCandidate :
      TransitionTableCandidate root

    stateRepresentative :
      (state :
        Fin
          (stateCount transitionCandidate)) →
      CandidateStateRepresentative
        transitionCandidate
        state

open FiniteQ1Candidate public

------------------------------------------------------------------------
-- Admission compiles DATA to the stronger reachable/rewrite-generated owner.
------------------------------------------------------------------------

admitFiniteQ1Candidate :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (candidate : FiniteQ1Candidate root) →
  GeneratedSemanticCongruence
    (transitionCandidate candidate) →
  Reachable.ReachableRewriteGeneratedClosedQuotient root
admitFiniteQ1Candidate candidate congruence =
  Reachable.reachable-rewrite-generated-closed-quotient
    generated
    admittedRepresentative
  where
    transition :
      TransitionTableCandidate root
    transition =
      transitionCandidate candidate

    generated :
      Generated.TransitionGeneratedRestrictionQuotient root
    generated =
      admitTransitionTableCandidate transition congruence

    admittedRepresentative :
      (state : Fin (Generated.stateCount generated)) →
      Reachable.ReachableStateRepresentative generated state
    admittedRepresentative state =
      Reachable.reachable-state-representative
        (CandidateStateRepresentative.currentVariables source)
        (CandidateStateRepresentative.formula source)
        (CandidateStateRepresentative.derivation source)
        (CandidateStateRepresentative.selectsState source)
        (CandidateStateRepresentative.strictlySmallerThanRoot source)
        (CandidateStateRepresentative.rewriteProgram source)
      where
        source :
          CandidateStateRepresentative transition state
        source =
          stateRepresentative candidate state

------------------------------------------------------------------------
-- State-specific admitted witness.
------------------------------------------------------------------------

record AdmittedFiniteQ1StateWitness
    (state : Q2.BoundedSelfReferenceState) : Set₁ where
  constructor admitted-finite-q1-state-witness
  field
    candidate :
      FiniteQ1Candidate
        (Bridge.cookToIndexed
          (Q2.currentFormula state))

    semanticCongruence :
      GeneratedSemanticCongruence
        (transitionCandidate candidate)

    allOverheadFits :
      Q1.ClosedQuotientAllOverheadFits
        (RewriteGenerated.toClosedStrictRepresentativeQuotient
          (Reachable.toRewriteGeneratedClosedQuotient
            (admitFiniteQ1Candidate
              candidate
              semanticCongruence)))
        (Recurrence.stateOverhead state)

open AdmittedFiniteQ1StateWitness public

admittedFiniteToReachableWitness :
  ∀ {state : Q2.BoundedSelfReferenceState} →
  AdmittedFiniteQ1StateWitness state →
  Reachable.ReachableRewriteGeneratedQ1StateWitness state
admittedFiniteToReachableWitness admitted =
  admitFiniteQ1Candidate
    (candidate admitted)
    (semanticCongruence admitted)
  ,
  allOverheadFits admitted

------------------------------------------------------------------------
-- Machine execution returns only finite DATA.
--
-- The output candidate is literally part of the terminal machine state.  No
-- decoder is permitted to manufacture semantic admission proofs.
------------------------------------------------------------------------

data CandidateMachineState
    {rootVariables : Nat}
    (root : SAT.BooleanFormula rootVariables)
    (Work : Set) : Set₁ where
  working :
    Work →
    CandidateMachineState root Work

  finished :
    FiniteQ1Candidate root →
    CandidateMachineState root Work

candidateMachineStep :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    {Work : Set} →
  (Work → CandidateMachineState root Work) →
  CandidateMachineState root Work →
  CandidateMachineState root Work
candidateMachineStep advance (working work) =
  advance work
candidateMachineStep advance (finished candidate) =
  finished candidate

record FiniteCandidateConstructionRun
    (state : Q2.BoundedSelfReferenceState) : Set₁ where
  constructor finite-candidate-construction-run
  field
    Work : Set

    advance :
      Work →
      CandidateMachineState
        (Bridge.cookToIndexed
          (Q2.currentFormula state))
        Work

    initialWork : Work

    finiteCandidate :
      FiniteQ1Candidate
        (Bridge.cookToIndexed
          (Q2.currentFormula state))

    machineStepCount : Nat

    machineExecution :
      Executed.Iterates
        (candidateMachineStep advance)
        machineStepCount
        (working initialWork)
        (finished finiteCandidate)

open FiniteCandidateConstructionRun public

------------------------------------------------------------------------
-- Admission is attached OUTSIDE the construction machine.
------------------------------------------------------------------------

record AdmittedFiniteCandidateConstructionRun
    (state : Q2.BoundedSelfReferenceState) : Set₁ where
  constructor admitted-finite-candidate-construction-run
  field
    construction :
      FiniteCandidateConstructionRun state

    semanticCongruence :
      GeneratedSemanticCongruence
        (transitionCandidate
          (finiteCandidate construction))

    allOverheadFits :
      Q1.ClosedQuotientAllOverheadFits
        (RewriteGenerated.toClosedStrictRepresentativeQuotient
          (Reachable.toRewriteGeneratedClosedQuotient
            (admitFiniteQ1Candidate
              (finiteCandidate construction)
              semanticCongruence)))
        (Recurrence.stateOverhead state)

    machineConstructionAndNextStrict :
      (Operational.q1WitnessGraphCellCount
        (Reachable.toRewriteGeneratedQ1StateWitness
          (admittedFiniteToReachableWitness
            (admitted-finite-q1-state-witness
              (finiteCandidate construction)
              semanticCongruence
              allOverheadFits)))
        + machineStepCount construction)
      +
      Q2.recursiveMeasure
        (Charged.q1WitnessNextState
          state
          (Reachable.toRewriteGeneratedQ1StateWitness
            (admittedFiniteToReachableWitness
              (admitted-finite-q1-state-witness
                (finiteCandidate construction)
                semanticCongruence
                allOverheadFits))))
      <
      Q2.recursiveMeasure state

open AdmittedFiniteCandidateConstructionRun public

admittedRunQ1Witness :
  ∀ {state : Q2.BoundedSelfReferenceState} →
  AdmittedFiniteCandidateConstructionRun state →
  Recurrence.Q1StateWitness state
admittedRunQ1Witness admitted =
  Reachable.toRewriteGeneratedQ1StateWitness
    (admittedFiniteToReachableWitness
      (admitted-finite-q1-state-witness
        (finiteCandidate
          (construction admitted))
        (semanticCongruence admitted)
        (allOverheadFits admitted)))

------------------------------------------------------------------------
-- Compatibility compiler to the existing operational Q1 interface.
--
-- The old List Unit field is now DERIVED from a real typed machine execution
-- count.  It is not the source of authority.
------------------------------------------------------------------------

admittedFiniteRunToOperationalRun :
  ∀ {state : Q2.BoundedSelfReferenceState} →
  AdmittedFiniteCandidateConstructionRun state →
  Operational.OperationalQ1ConstructionRun state
admittedFiniteRunToOperationalRun {state} admitted =
  record
    { Operational.q1Witness =
        witness

    ; Operational.emittedFalseTarget =
        λ stateIndex →
          Quotient.step
            (Operational.q1WitnessQuotient witness)
            stateIndex
            false

    ; Operational.emittedTrueTarget =
        λ stateIndex →
          Quotient.step
            (Operational.q1WitnessQuotient witness)
            stateIndex
            true

    ; Operational.emittedFalseTargetExact =
        λ stateIndex → refl

    ; Operational.emittedTrueTargetExact =
        λ stateIndex → refl

    ; Operational.auxiliaryTrace =
        Executed.unitTrace
          (machineStepCount
            (construction admitted))

    ; Operational.operationalAndNextStrict =
        strict
    }
  where
    witness :
      Recurrence.Q1StateWitness state
    witness =
      admittedRunQ1Witness admitted

    strict :
      (Operational.q1WitnessGraphCellCount witness
        +
        Data.List.Base.length
          (Operational.unitTrace
            (machineStepCount
              (construction admitted))))
      +
      Q2.recursiveMeasure
        (Charged.q1WitnessNextState state witness)
      <
      Q2.recursiveMeasure state
    strict
      rewrite
        Executed.unitTraceLengthExact
          (machineStepCount
            (construction admitted)) =
      machineConstructionAndNextStrict admitted

AdmittedFiniteCandidateStateConstructor : Set₁
AdmittedFiniteCandidateStateConstructor =
  (state : Q2.BoundedSelfReferenceState) →
  Maybe (AdmittedFiniteCandidateConstructionRun state)

admittedFiniteConstructorToOperational :
  AdmittedFiniteCandidateStateConstructor →
  Operational.OperationalQ1StateConstructor
admittedFiniteConstructorToOperational constructor state
    with constructor state
... | nothing =
  nothing
... | just admitted =
  just (admittedFiniteRunToOperationalRun admitted)

admittedFiniteConstructorToQ2StepSystem :
  AdmittedFiniteCandidateStateConstructor →
  Q2.BoundedSelfReferenceStepSystem
admittedFiniteConstructorToQ2StepSystem constructor =
  Operational.operationalConstructorToQ2StepSystem
    (admittedFiniteConstructorToOperational constructor)

------------------------------------------------------------------------
-- AUTHORITY BOUNDARY
--
-- Machine execution can emit only finite candidate data.
--
-- Semantic congruence and all-overhead fit are not decoder outputs.  They are
-- proof obligations attached to the exact terminal candidate after execution.
--
-- Thus an intermediate machine state cannot borrow the final candidate's
-- semantic authority, and the machine cannot return an admitted quotient by
-- construction alone.
------------------------------------------------------------------------
