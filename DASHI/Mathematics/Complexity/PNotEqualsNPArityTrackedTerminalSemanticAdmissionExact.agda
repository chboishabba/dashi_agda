module DASHI.Mathematics.Complexity.PNotEqualsNPArityTrackedTerminalSemanticAdmissionExact where

------------------------------------------------------------------------
-- ARITY-TRACKED TERMINAL OBSERVATIONS -> FULL GENERATED SEMANTIC CONGRUENCE
--
-- Goal:
--   remove GeneratedSemanticCongruence as a direct admission premise.
--
-- A finite transition-table candidate is instead equipped with:
--
--   * stateArity : State -> Nat
--   * proof that every reachable derivation's selected state records its
--     actual remaining arity
--   * terminalLabel : State -> Bool
--   * proof that at arity zero, terminalLabel equals literal structural
--     evaluation of the reachable zero-variable formula.
--
-- From this LOCAL data:
--
--   equal generated state
--      -> same remaining arity
--      -> same current terminal/nonterminal observation
--      -> relation is preserved by every common Shannon restriction
--      -> canonical FutureEquivalent
--      -> same residual Boolean function
--      -> ordinary satisfiability equivalence.
--
-- No SAT decision oracle is used in this derivation.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Fin.Base using (Fin)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Core.TypedDependencyCore as Dependency
import DASHI.Core.AdmissibleReachability as Reachability
import DASHI.Core.FutureObservationalRefinement as Future

import DASHI.Mathematics.Complexity.BooleanFormulaSATSelfReductionExact as SAT
import DASHI.Mathematics.Complexity.PNotEqualsNPSelfDiagonalRestrictionFamilyExact as Family
import DASHI.Mathematics.Complexity.PNotEqualsNPSelfDiagonalFutureCongruenceExact as FutureSAT
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1FiniteCandidateSemanticAdmissionExact as Candidate
import DASHI.Mathematics.Complexity.PNotEqualsNPResourceClosingRestrictionQuotientExact as Quotient
import DASHI.Mathematics.Complexity.PNotEqualsNPRewriteGeneratedQ1DiscoveryExact as RewriteGenerated
import DASHI.Mathematics.Complexity.PNotEqualsNPReachableRewriteGeneratedQ1Exact as Reachable
import DASHI.Mathematics.Complexity.PNotEqualsNPSelfReferenceAllOverheadBudgetExact as Q1
import DASHI.Mathematics.Complexity.PNotEqualsNPBoundedSelfReferenceWellFoundedExact as Q2
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1ReachableStateRecurrenceExact as Recurrence
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1OperationalConstructionCostExact as Operational
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1ConstructionChargedRecurrenceExact as Charged

------------------------------------------------------------------------
-- Local terminal/arity admission data.
------------------------------------------------------------------------

record ArityTrackedTerminalAdmission
    {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (candidate : Candidate.TransitionTableCandidate root) : Set₁ where
  constructor arity-tracked-terminal-admission
  field
    stateArity :
      Fin (Candidate.stateCount candidate) →
      Nat

    selectedStateArityExact :
      ∀ {currentVariables : Nat}
        {current : SAT.BooleanFormula currentVariables}
        (derivation :
          Family.RestrictionDerivation root current) →
      stateArity
        (Candidate.candidateSelect candidate derivation)
      ≡
      currentVariables

    terminalLabel :
      Fin (Candidate.stateCount candidate) →
      Bool

    terminalLabelCorrect :
      ∀ {terminal : SAT.BooleanFormula zero}
        (derivation :
          Family.RestrictionDerivation root terminal) →
      terminalLabel
        (Candidate.candidateSelect candidate derivation)
      ≡
      SAT.evaluate terminal FutureSAT.emptyAssignment

open ArityTrackedTerminalAdmission public

------------------------------------------------------------------------
-- Same generated state automatically implies same remaining arity.
------------------------------------------------------------------------

sameSelectedStateImpliesSameArity :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    {candidate : Candidate.TransitionTableCandidate root}
    (admission : ArityTrackedTerminalAdmission candidate)
    {leftVariables rightVariables : Nat}
    {left : SAT.BooleanFormula leftVariables}
    {right : SAT.BooleanFormula rightVariables}
    (leftDerivation : Family.RestrictionDerivation root left)
    (rightDerivation : Family.RestrictionDerivation root right) →
  Candidate.candidateSelect candidate leftDerivation
  ≡
  Candidate.candidateSelect candidate rightDerivation →
  leftVariables ≡ rightVariables
sameSelectedStateImpliesSameArity
    admission
    leftDerivation
    rightDerivation
    sameState =
  trans
    (sym
      (selectedStateArityExact admission leftDerivation))
    (trans
      (cong
        (stateArity admission)
        sameState)
      (selectedStateArityExact admission rightDerivation))

------------------------------------------------------------------------
-- Generated-state equality as a relation on reachable restriction nodes.
------------------------------------------------------------------------

SameGeneratedState :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (candidate : Candidate.TransitionTableCandidate root) →
  Family.RestrictionNode root →
  Family.RestrictionNode root →
  Set
SameGeneratedState candidate left right =
  Candidate.candidateSelect
    candidate
    (Family.derivation left)
  ≡
  Candidate.candidateSelect
    candidate
    (Family.derivation right)

------------------------------------------------------------------------
-- Current observer equality follows from local terminal labels.
------------------------------------------------------------------------

sameGeneratedStateRefinesCurrent :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    {candidate : Candidate.TransitionTableCandidate root}
    (admission : ArityTrackedTerminalAdmission candidate)
    {left right : Family.RestrictionNode root} →
  SameGeneratedState candidate left right →
  Future.CurrentEquivalent
    FutureSAT.restrictionObservation
    left
    right
sameGeneratedStateRefinesCurrent
    admission
    {left}
    {right}
    sameState
    with Family.currentVariables left
       | Family.currentVariables right
       | sameSelectedStateImpliesSameArity
           admission
           (Family.derivation left)
           (Family.derivation right)
           sameState
... | zero | .zero | refl =
  cong FutureSAT.terminal
    (trans
      (sym
        (terminalLabelCorrect
          admission
          (Family.derivation left)))
      (trans
        (cong
          (terminalLabel admission)
          sameState)
        (terminalLabelCorrect
          admission
          (Family.derivation right))))
... | suc remaining | .(suc remaining) | refl =
  refl

------------------------------------------------------------------------
-- One common Shannon action preserves generated-state equality.
------------------------------------------------------------------------

sameGeneratedStateAfterCommonRestriction :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    {candidate : Candidate.TransitionTableCandidate root}
    {left right : Family.RestrictionNode root}
    {bit : Bool} →
  SameGeneratedState candidate left right →
  (leftAdmissible : FutureSAT.NonTerminal left) →
  (rightAdmissible : FutureSAT.NonTerminal right) →
  SameGeneratedState
    candidate
    (FutureSAT.restrictedNode left bit leftAdmissible)
    (FutureSAT.restrictedNode right bit rightAdmissible)
sameGeneratedStateAfterCommonRestriction
    {candidate = candidate}
    {left}
    {right}
    {bit}
    sameState
    (leftRemaining , leftArity)
    (rightRemaining , rightArity)
    with leftArity | rightArity | bit
... | refl | refl | false =
  cong
    (λ state →
      Candidate.step candidate state false)
    sameState
... | refl | refl | true =
  cong
    (λ state →
      Candidate.step candidate state true)
    sameState

------------------------------------------------------------------------
-- The relation is closed under arbitrary common admissible traces.
------------------------------------------------------------------------

sameGeneratedStateClosedUnderCommonTrace :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    {candidate : Candidate.TransitionTableCandidate root}
    {actions}
    {left right leftAfter rightAfter :
      Family.RestrictionNode root} →
  SameGeneratedState candidate left right →
  Reachability.Executes
    (FutureSAT.restrictionActionSystem root)
    actions
    left
    leftAfter →
  Reachability.Executes
    (FutureSAT.restrictionActionSystem root)
    actions
    right
    rightAfter →
  SameGeneratedState candidate leftAfter rightAfter
sameGeneratedStateClosedUnderCommonTrace
    related
    Reachability.executesNil
    Reachability.executesNil =
  related
sameGeneratedStateClosedUnderCommonTrace
    {candidate = candidate}
    related
    (Reachability.executesCons leftAction leftRest)
    (Reachability.executesCons rightAction rightRest) =
  sameGeneratedStateClosedUnderCommonTrace
    nextRelated
    leftRest
    rightRest
  where
    leftProof :
      FutureSAT.NonTerminal _
    leftProof =
      proj₁
        (Dependency.postcondition leftAction)

    rightProof :
      FutureSAT.NonTerminal _
    rightProof =
      proj₁
        (Dependency.postcondition rightAction)

    leftAfterExact :
      Dependency.after leftAction
      ≡
      FutureSAT.restrictedNode _ _ leftProof
    leftAfterExact =
      proj₂
        (Dependency.postcondition leftAction)

    rightAfterExact :
      Dependency.after rightAction
      ≡
      FutureSAT.restrictedNode _ _ rightProof
    rightAfterExact =
      proj₂
        (Dependency.postcondition rightAction)

    restrictedRelated :
      SameGeneratedState
        candidate
        (FutureSAT.restrictedNode _ _ leftProof)
        (FutureSAT.restrictedNode _ _ rightProof)
    restrictedRelated =
      sameGeneratedStateAfterCommonRestriction
        related
        leftProof
        rightProof

    nextRelated :
      SameGeneratedState
        candidate
        (Dependency.after leftAction)
        (Dependency.after rightAction)
    nextRelated
      rewrite leftAfterExact | rightAfterExact =
      restrictedRelated

------------------------------------------------------------------------
-- Therefore generated-state equality is a dynamically congruent refinement.
------------------------------------------------------------------------

sameGeneratedStateIsDynamicallyCongruent :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    {candidate : Candidate.TransitionTableCandidate root} →
  ArityTrackedTerminalAdmission candidate →
  Future.DynamicallyCongruentRefinement
    (FutureSAT.restrictionActionSystem root)
    FutureSAT.restrictionObservation
    (SameGeneratedState candidate)
sameGeneratedStateIsDynamicallyCongruent admission =
  Future.dynamicallyCongruentRefinement
    (sameGeneratedStateRefinesCurrent admission)
    sameGeneratedStateClosedUnderCommonTrace

sameGeneratedStateContainedInFutureEquivalent :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    {candidate : Candidate.TransitionTableCandidate root}
    (admission : ArityTrackedTerminalAdmission candidate)
    {left right : Family.RestrictionNode root} →
  SameGeneratedState candidate left right →
  Future.FutureEquivalent
    (FutureSAT.restrictionActionSystem root)
    FutureSAT.restrictionObservation
    left
    right
sameGeneratedStateContainedInFutureEquivalent admission =
  Future.anyCongruentRefinementIsContainedInFutureEquivalent
    (sameGeneratedStateIsDynamicallyCongruent admission)

------------------------------------------------------------------------
-- Main result: LOCAL arity + terminal-label correctness pays GLOBAL semantic
-- congruence for the generated transition table.
------------------------------------------------------------------------

arityTerminalAdmissionBuildsSemanticCongruence :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    {candidate : Candidate.TransitionTableCandidate root} →
  ArityTrackedTerminalAdmission candidate →
  Candidate.GeneratedSemanticCongruence candidate
arityTerminalAdmissionBuildsSemanticCongruence
    {root = root}
    {candidate = candidate}
    admission
    leftDerivation
    rightDerivation
    sameState =
  FutureSAT.futureEquivalentImpliesSatisfiabilityEquivalent
    sameArity
    future
  where
    leftNode :
      Family.RestrictionNode root
    leftNode =
      Family.restriction-node
        _
        _
        leftDerivation

    rightNode :
      Family.RestrictionNode root
    rightNode =
      Family.restriction-node
        _
        _
        rightDerivation

    sameArity :
      Family.currentVariables leftNode
      ≡
      Family.currentVariables rightNode
    sameArity =
      sameSelectedStateImpliesSameArity
        admission
        leftDerivation
        rightDerivation
        sameState

    future :
      Future.FutureEquivalent
        (FutureSAT.restrictionActionSystem root)
        FutureSAT.restrictionObservation
        leftNode
        rightNode
    future =
      sameGeneratedStateContainedInFutureEquivalent
        admission
        sameState

------------------------------------------------------------------------
-- Compile local arity/terminal admission to the existing admitted construction
-- run.  GeneratedSemanticCongruence is DERIVED, not supplied.
------------------------------------------------------------------------

derivedClosedQ1 :
  ∀ {state : Q2.BoundedSelfReferenceState}
    (construction : Candidate.FiniteCandidateConstructionRun state)
    (admission :
      ArityTrackedTerminalAdmission
        (Candidate.transitionCandidate
          (Candidate.finiteCandidate construction))) →
  RewriteGenerated.toClosedStrictRepresentativeQuotient
    (Reachable.toRewriteGeneratedClosedQuotient
      (Candidate.admitFiniteQ1Candidate
        (Candidate.finiteCandidate construction)
        (arityTerminalAdmissionBuildsSemanticCongruence admission)))
  ≡
  RewriteGenerated.toClosedStrictRepresentativeQuotient
    (Reachable.toRewriteGeneratedClosedQuotient
      (Candidate.admitFiniteQ1Candidate
        (Candidate.finiteCandidate construction)
        (arityTerminalAdmissionBuildsSemanticCongruence admission)))
derivedClosedQ1 construction admission =
  refl

record ArityTerminalAdmittedConstructionRun
    (state : Q2.BoundedSelfReferenceState) : Set₁ where
  constructor arity-terminal-admitted-construction-run
  field
    construction :
      Candidate.FiniteCandidateConstructionRun state

    localAdmission :
      ArityTrackedTerminalAdmission
        (Candidate.transitionCandidate
          (Candidate.finiteCandidate construction))

    allOverheadFits :
      Q1.ClosedQuotientAllOverheadFits
        (RewriteGenerated.toClosedStrictRepresentativeQuotient
          (Reachable.toRewriteGeneratedClosedQuotient
            (Candidate.admitFiniteQ1Candidate
              (Candidate.finiteCandidate construction)
              (arityTerminalAdmissionBuildsSemanticCongruence
                localAdmission))))
        (Recurrence.stateOverhead state)

    machineConstructionAndNextStrict :
      (Operational.q1WitnessGraphCellCount
        (RewriteGenerated.rewriteGeneratedWitnessToLegacy
          (Reachable.toRewriteGeneratedQ1StateWitness
            (Candidate.admittedFiniteToReachableWitness
              (Candidate.admitted-finite-q1-state-witness
                (Candidate.finiteCandidate construction)
                (arityTerminalAdmissionBuildsSemanticCongruence
                  localAdmission)
                allOverheadFits))))
        + Candidate.machineStepCount construction)
      +
      Q2.recursiveMeasure
        (Charged.q1WitnessNextState
          state
          (RewriteGenerated.rewriteGeneratedWitnessToLegacy
            (Reachable.toRewriteGeneratedQ1StateWitness
              (Candidate.admittedFiniteToReachableWitness
                (Candidate.admitted-finite-q1-state-witness
                  (Candidate.finiteCandidate construction)
                  (arityTerminalAdmissionBuildsSemanticCongruence
                    localAdmission)
                  allOverheadFits)))))
      <
      Q2.recursiveMeasure state

open ArityTerminalAdmittedConstructionRun public

arityTerminalRunToAdmittedFiniteRun :
  ∀ {state : Q2.BoundedSelfReferenceState} →
  ArityTerminalAdmittedConstructionRun state →
  Candidate.AdmittedFiniteCandidateConstructionRun state
arityTerminalRunToAdmittedFiniteRun run =
  Candidate.admitted-finite-candidate-construction-run
    (construction run)
    (arityTerminalAdmissionBuildsSemanticCongruence
      (localAdmission run))
    (allOverheadFits run)
    (machineConstructionAndNextStrict run)

ArityTerminalAdmittedStateConstructor : Set₁
ArityTerminalAdmittedStateConstructor =
  (state : Q2.BoundedSelfReferenceState) →
  Maybe (ArityTerminalAdmittedConstructionRun state)

arityTerminalConstructorToAdmittedFinite :
  ArityTerminalAdmittedStateConstructor →
  Candidate.AdmittedFiniteCandidateStateConstructor
arityTerminalConstructorToAdmittedFinite constructor state
    with constructor state
... | nothing =
  nothing
... | just run =
  just (arityTerminalRunToAdmittedFiniteRun run)

arityTerminalConstructorToQ2StepSystem :
  ArityTerminalAdmittedStateConstructor →
  Q2.BoundedSelfReferenceStepSystem
arityTerminalConstructorToQ2StepSystem constructor =
  Candidate.admittedFiniteConstructorToQ2StepSystem
    (arityTerminalConstructorToAdmittedFinite constructor)

------------------------------------------------------------------------
-- Stronger consequence: same generated state at a tracked layer determines
-- the entire residual Boolean function, not only SAT truth.
------------------------------------------------------------------------

sameGeneratedStateImpliesResidualFunctionEquality :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    {candidate : Candidate.TransitionTableCandidate root}
    (admission : ArityTrackedTerminalAdmission candidate)
    {left right : Family.RestrictionNode root} →
  SameGeneratedState candidate left right →
  FutureSAT.SameLayerResidualFunction left right
sameGeneratedStateImpliesResidualFunctionEquality
    admission
    {left}
    {right}
    sameState =
  FutureSAT.futureEquivalentGivesSameLayerResidualFunction
    sameArity
    (sameGeneratedStateContainedInFutureEquivalent
      admission
      sameState)
  where
    sameArity :
      Family.currentVariables left
      ≡
      Family.currentVariables right
    sameArity =
      sameSelectedStateImpliesSameArity
        admission
        (Family.derivation left)
        (Family.derivation right)
        sameState

------------------------------------------------------------------------
-- FRONTIER CONSEQUENCE
--
-- Removed as a primitive admission theorem:
--   GeneratedSemanticCongruence.
--
-- Replaced by local finite-automaton obligations:
--   * selected state tracks remaining arity;
--   * terminal state label agrees with literal zero-variable evaluation.
--
-- Once those are proved, dynamic/future safety and full residual-function
-- equality are inherited from the existing Shannon future-observation theory.
------------------------------------------------------------------------
