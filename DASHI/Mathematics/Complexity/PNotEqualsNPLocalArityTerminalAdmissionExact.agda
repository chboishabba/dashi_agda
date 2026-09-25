module DASHI.Mathematics.Complexity.PNotEqualsNPLocalArityTerminalAdmissionExact where

------------------------------------------------------------------------
-- LOCAL TRANSITION ARITY LAWS -> GLOBAL SELECTED-STATE ARITY TRACKING
--
-- Strengthens:
--   PNotEqualsNPArityTrackedTerminalSemanticAdmissionExact
--
-- Instead of supplying:
--
--   selectedStateArityExact
--
-- for every reachable derivation, it is enough to prove:
--
--   * root state has the root arity;
--   * false/true transition from a state of arity suc n lands in arity n.
--
-- The global selected-state arity theorem is then derived by structural
-- induction on RestrictionDerivation.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Fin.Base using (Fin)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (sym; trans)

import DASHI.Mathematics.Complexity.BooleanFormulaSATSelfReductionExact as SAT
import DASHI.Mathematics.Complexity.PNotEqualsNPSelfDiagonalRestrictionFamilyExact as Family
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1FiniteCandidateSemanticAdmissionExact as Candidate
import DASHI.Mathematics.Complexity.PNotEqualsNPArityTrackedTerminalSemanticAdmissionExact as ArityTerminal
import DASHI.Mathematics.Complexity.PNotEqualsNPBoundedSelfReferenceWellFoundedExact as Q2

------------------------------------------------------------------------
-- Local finite automaton admission.
------------------------------------------------------------------------

record LocalArityTerminalAdmission
    {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (candidate : Candidate.TransitionTableCandidate root) : Set₁ where
  constructor local-arity-terminal-admission
  field
    stateArity :
      Fin (Candidate.stateCount candidate) →
      Nat

    rootStateArityExact :
      stateArity
        (Candidate.rootState candidate)
      ≡
      rootVariables

    falseStepArityExact :
      (state : Fin (Candidate.stateCount candidate))
      (remaining : Nat) →
      stateArity state ≡ suc remaining →
      stateArity
        (Candidate.step candidate state false)
      ≡
      remaining

    trueStepArityExact :
      (state : Fin (Candidate.stateCount candidate))
      (remaining : Nat) →
      stateArity state ≡ suc remaining →
      stateArity
        (Candidate.step candidate state true)
      ≡
      remaining

    terminalLabel :
      Fin (Candidate.stateCount candidate) →
      Bool

    terminalLabelCorrect :
      ∀ {terminal : SAT.BooleanFormula 0}
        (derivation :
          Family.RestrictionDerivation root terminal) →
      terminalLabel
        (Candidate.candidateSelect candidate derivation)
      ≡
      SAT.evaluate
        terminal
        ArityTerminal.FutureSAT.emptyAssignment

open LocalArityTerminalAdmission public

------------------------------------------------------------------------
-- Derive global arity tracking by induction on the literal restriction proof.
------------------------------------------------------------------------

selectedStateArityFromLocal :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    {candidate : Candidate.TransitionTableCandidate root}
    (local : LocalArityTerminalAdmission candidate)
    {currentVariables : Nat}
    {current : SAT.BooleanFormula currentVariables}
    (derivation : Family.RestrictionDerivation root current) →
  stateArity local
    (Candidate.candidateSelect candidate derivation)
  ≡
  currentVariables
selectedStateArityFromLocal
    {candidate = candidate}
    local
    Family.restrictionRoot =
  rootStateArityExact local

selectedStateArityFromLocal
    {candidate = candidate}
    local
    (Family.restrictionFalse
      {currentVariables = currentVariables}
      derivation) =
  falseStepArityExact
    local
    (Candidate.candidateSelect candidate derivation)
    currentVariables
    (selectedStateArityFromLocal local derivation)

selectedStateArityFromLocal
    {candidate = candidate}
    local
    (Family.restrictionTrue
      {currentVariables = currentVariables}
      derivation) =
  trueStepArityExact
    local
    (Candidate.candidateSelect candidate derivation)
    currentVariables
    (selectedStateArityFromLocal local derivation)

------------------------------------------------------------------------
-- Compile local laws to the prior arity/terminal admission.
------------------------------------------------------------------------

localBuildsArityTrackedTerminalAdmission :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    {candidate : Candidate.TransitionTableCandidate root} →
  LocalArityTerminalAdmission candidate →
  ArityTerminal.ArityTrackedTerminalAdmission candidate
localBuildsArityTrackedTerminalAdmission local =
  ArityTerminal.arity-tracked-terminal-admission
    (stateArity local)
    (selectedStateArityFromLocal local)
    (terminalLabel local)
    (terminalLabelCorrect local)

localArityTerminalBuildsSemanticCongruence :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    {candidate : Candidate.TransitionTableCandidate root} →
  LocalArityTerminalAdmission candidate →
  Candidate.GeneratedSemanticCongruence candidate
localArityTerminalBuildsSemanticCongruence local =
  ArityTerminal.arityTerminalAdmissionBuildsSemanticCongruence
    (localBuildsArityTrackedTerminalAdmission local)

------------------------------------------------------------------------
-- Lift the local admission to the construction path.
------------------------------------------------------------------------

record LocalArityTerminalAdmittedConstructionRun
    (state : Q2.BoundedSelfReferenceState) : Set₁ where
  constructor local-arity-terminal-admitted-construction-run
  field
    arityTerminalRun :
      ArityTerminal.ArityTerminalAdmittedConstructionRun state

    localAdmission :
      LocalArityTerminalAdmission
        (Candidate.transitionCandidate
          (Candidate.finiteCandidate
            (ArityTerminal.construction arityTerminalRun)))

    localAdmissionAgrees :
      ArityTerminal.localAdmission arityTerminalRun
      ≡
      localBuildsArityTrackedTerminalAdmission localAdmission

open LocalArityTerminalAdmittedConstructionRun public

localRunToArityTerminalRun :
  ∀ {state : Q2.BoundedSelfReferenceState} →
  LocalArityTerminalAdmittedConstructionRun state →
  ArityTerminal.ArityTerminalAdmittedConstructionRun state
localRunToArityTerminalRun run =
  arityTerminalRun run

LocalArityTerminalAdmittedStateConstructor : Set₁
LocalArityTerminalAdmittedStateConstructor =
  (state : Q2.BoundedSelfReferenceState) →
  Maybe (LocalArityTerminalAdmittedConstructionRun state)

localConstructorToArityTerminal :
  LocalArityTerminalAdmittedStateConstructor →
  ArityTerminal.ArityTerminalAdmittedStateConstructor
localConstructorToArityTerminal constructor state
    with constructor state
... | nothing =
  nothing
... | just run =
  just (localRunToArityTerminalRun run)

localConstructorToQ2StepSystem :
  LocalArityTerminalAdmittedStateConstructor →
  Q2.BoundedSelfReferenceStepSystem
localConstructorToQ2StepSystem constructor =
  ArityTerminal.arityTerminalConstructorToQ2StepSystem
    (localConstructorToArityTerminal constructor)

------------------------------------------------------------------------
-- FRONTIER CONSEQUENCE
--
-- Global arity tracking is no longer a primitive theorem.
--
-- Remaining local semantic admission:
--   * root arity;
--   * one-step arity decrement on false/true;
--   * zero-variable terminal label correctness.
------------------------------------------------------------------------
