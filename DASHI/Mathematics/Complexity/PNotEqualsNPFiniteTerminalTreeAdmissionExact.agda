module DASHI.Mathematics.Complexity.PNotEqualsNPFiniteTerminalTreeAdmissionExact where

------------------------------------------------------------------------
-- FINITE TERMINAL VERIFICATION TREE
--
-- The previous strongest Q1 admission still asked for the global theorem
--
--   terminalLabelCorrect :
--     every zero-variable RestrictionDerivation has the right label.
--
-- This owner removes that theorem from the primitive interface.
--
-- A finite binary verification tree is indexed by the ACTUAL Boolean formula
-- and the ACTUAL transition-table state.  At each nonterminal formula it
-- contains the false/true child trees at the corresponding transition states;
-- at a zero-variable formula it contains only the literal structural
-- evaluation equality.
--
-- Any RestrictionDerivation can be replayed through the tree by induction.
-- Hence terminal-label correctness is derived from finite local leaf checks,
-- with no prefix-completeness theorem and no SAT oracle.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Fin.Base using (Fin)
open import Data.Maybe.Base using (Maybe; just; nothing)

import DASHI.Mathematics.Complexity.BooleanFormulaSATSelfReductionExact as SAT
import DASHI.Mathematics.Complexity.PNotEqualsNPSelfDiagonalRestrictionFamilyExact as Family
import DASHI.Mathematics.Complexity.PNotEqualsNPSelfDiagonalFutureCongruenceExact as FutureSAT
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1FiniteCandidateSemanticAdmissionExact as Candidate
import DASHI.Mathematics.Complexity.PNotEqualsNPLocalArityTerminalAdmissionExact as Local
import DASHI.Mathematics.Complexity.PNotEqualsNPBoundedSelfReferenceWellFoundedExact as Q2
import DASHI.Mathematics.Complexity.PNotEqualsNPSelfReferenceAllOverheadBudgetExact as Q1
import DASHI.Mathematics.Complexity.PNotEqualsNPReachableRewriteGeneratedQ1Exact as Reachable
import DASHI.Mathematics.Complexity.PNotEqualsNPRewriteGeneratedQ1DiscoveryExact as RewriteGenerated
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1ReachableStateRecurrenceExact as Recurrence
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1OperationalConstructionCostExact as Operational
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1ConstructionChargedRecurrenceExact as Charged

------------------------------------------------------------------------
-- Finite verification tree.
------------------------------------------------------------------------

data TerminalVerificationTree
    {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (candidate : Candidate.TransitionTableCandidate root)
    (terminalLabel : Fin (Candidate.stateCount candidate) → Bool) :
    ∀ {variables : Nat} →
    SAT.BooleanFormula variables →
    Fin (Candidate.stateCount candidate) →
    Set₁ where

  terminalLeaf :
    ∀ {formula : SAT.BooleanFormula zero}
      {state : Fin (Candidate.stateCount candidate)} →
    terminalLabel state
    ≡
    SAT.evaluate formula FutureSAT.emptyAssignment →
    TerminalVerificationTree
      candidate
      terminalLabel
      formula
      state

  branch :
    ∀ {variables : Nat}
      {formula : SAT.BooleanFormula (suc variables)}
      {state : Fin (Candidate.stateCount candidate)} →
    TerminalVerificationTree
      candidate
      terminalLabel
      (SAT.restrictHead false formula)
      (Candidate.step candidate state false) →
    TerminalVerificationTree
      candidate
      terminalLabel
      (SAT.restrictHead true formula)
      (Candidate.step candidate state true) →
    TerminalVerificationTree
      candidate
      terminalLabel
      formula
      state

------------------------------------------------------------------------
-- Child projections are total because the index rules out terminalLeaf at
-- positive arity.
------------------------------------------------------------------------

falseSubtree :
  ∀ {rootVariables variables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    {candidate : Candidate.TransitionTableCandidate root}
    {terminalLabel : Fin (Candidate.stateCount candidate) → Bool}
    {formula : SAT.BooleanFormula (suc variables)}
    {state : Fin (Candidate.stateCount candidate)} →
  TerminalVerificationTree candidate terminalLabel formula state →
  TerminalVerificationTree
    candidate
    terminalLabel
    (SAT.restrictHead false formula)
    (Candidate.step candidate state false)
falseSubtree (branch falseTree trueTree) =
  falseTree

trueSubtree :
  ∀ {rootVariables variables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    {candidate : Candidate.TransitionTableCandidate root}
    {terminalLabel : Fin (Candidate.stateCount candidate) → Bool}
    {formula : SAT.BooleanFormula (suc variables)}
    {state : Fin (Candidate.stateCount candidate)} →
  TerminalVerificationTree candidate terminalLabel formula state →
  TerminalVerificationTree
    candidate
    terminalLabel
    (SAT.restrictHead true formula)
    (Candidate.step candidate state true)
trueSubtree (branch falseTree trueTree) =
  trueTree

------------------------------------------------------------------------
-- Replay any literal RestrictionDerivation through the finite tree.
------------------------------------------------------------------------

treeAtDerivation :
  ∀ {rootVariables currentVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    {candidate : Candidate.TransitionTableCandidate root}
    {terminalLabel : Fin (Candidate.stateCount candidate) → Bool}
    {current : SAT.BooleanFormula currentVariables} →
  TerminalVerificationTree
    candidate
    terminalLabel
    root
    (Candidate.rootState candidate) →
  (derivation : Family.RestrictionDerivation root current) →
  TerminalVerificationTree
    candidate
    terminalLabel
    current
    (Candidate.candidateSelect candidate derivation)
treeAtDerivation tree Family.restrictionRoot =
  tree

treeAtDerivation tree
    (Family.restrictionFalse derivation) =
  falseSubtree
    (treeAtDerivation tree derivation)

treeAtDerivation tree
    (Family.restrictionTrue derivation) =
  trueSubtree
    (treeAtDerivation tree derivation)

------------------------------------------------------------------------
-- Main payoff: global terminal-label correctness is derived.
------------------------------------------------------------------------

verificationTreeBuildsTerminalLabelCorrect :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    {candidate : Candidate.TransitionTableCandidate root}
    {terminalLabel : Fin (Candidate.stateCount candidate) → Bool} →
  TerminalVerificationTree
    candidate
    terminalLabel
    root
    (Candidate.rootState candidate) →
  ∀ {terminal : SAT.BooleanFormula zero}
    (derivation : Family.RestrictionDerivation root terminal) →
  terminalLabel
    (Candidate.candidateSelect candidate derivation)
  ≡
  SAT.evaluate terminal FutureSAT.emptyAssignment
verificationTreeBuildsTerminalLabelCorrect tree derivation
    with treeAtDerivation tree derivation
... | terminalLeaf exact =
  exact

------------------------------------------------------------------------
-- Local arity + finite tree admission.
------------------------------------------------------------------------

record TreeLocalArityTerminalAdmission
    {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (candidate : Candidate.TransitionTableCandidate root) : Set₁ where
  constructor tree-local-arity-terminal-admission
  field
    stateArity :
      Fin (Candidate.stateCount candidate) →
      Nat

    rootStateArityExact :
      stateArity (Candidate.rootState candidate)
      ≡
      rootVariables

    falseStepArityExact :
      (state : Fin (Candidate.stateCount candidate))
      (remaining : Nat) →
      stateArity state ≡ suc remaining →
      stateArity (Candidate.step candidate state false)
      ≡
      remaining

    trueStepArityExact :
      (state : Fin (Candidate.stateCount candidate))
      (remaining : Nat) →
      stateArity state ≡ suc remaining →
      stateArity (Candidate.step candidate state true)
      ≡
      remaining

    terminalLabel :
      Fin (Candidate.stateCount candidate) →
      Bool

    terminalVerification :
      TerminalVerificationTree
        candidate
        terminalLabel
        root
        (Candidate.rootState candidate)

open TreeLocalArityTerminalAdmission public

treeLocalBuildsLocalAdmission :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    {candidate : Candidate.TransitionTableCandidate root} →
  TreeLocalArityTerminalAdmission candidate →
  Local.LocalArityTerminalAdmission candidate
treeLocalBuildsLocalAdmission admission =
  Local.local-arity-terminal-admission
    (stateArity admission)
    (rootStateArityExact admission)
    (falseStepArityExact admission)
    (trueStepArityExact admission)
    (terminalLabel admission)
    (verificationTreeBuildsTerminalLabelCorrect
      (terminalVerification admission))

------------------------------------------------------------------------
-- Lift directly onto the live Q1 construction path.
------------------------------------------------------------------------

record TreeLocalArityTerminalAdmittedConstructionRun
    (state : Q2.BoundedSelfReferenceState) : Set₁ where
  constructor tree-local-arity-terminal-admitted-construction-run
  field
    construction :
      Candidate.FiniteCandidateConstructionRun state

    treeLocalAdmission :
      TreeLocalArityTerminalAdmission
        (Candidate.transitionCandidate
          (Candidate.finiteCandidate construction))

    allOverheadFits :
      Q1.ClosedQuotientAllOverheadFits
        (RewriteGenerated.toClosedStrictRepresentativeQuotient
          (Reachable.toRewriteGeneratedClosedQuotient
            (Candidate.admitFiniteQ1Candidate
              (Candidate.finiteCandidate construction)
              (Local.localArityTerminalBuildsSemanticCongruence
                (treeLocalBuildsLocalAdmission treeLocalAdmission)))))
        (Recurrence.stateOverhead state)

    machineConstructionAndNextStrict :
      (Operational.q1WitnessGraphCellCount
        (RewriteGenerated.rewriteGeneratedWitnessToLegacy
          (Reachable.toRewriteGeneratedQ1StateWitness
            (Candidate.admittedFiniteToReachableWitness
              (Candidate.admitted-finite-q1-state-witness
                (Candidate.finiteCandidate construction)
                (Local.localArityTerminalBuildsSemanticCongruence
                  (treeLocalBuildsLocalAdmission treeLocalAdmission))
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
                  (Local.localArityTerminalBuildsSemanticCongruence
                    (treeLocalBuildsLocalAdmission treeLocalAdmission))
                  allOverheadFits)))))
      <
      Q2.recursiveMeasure state

open TreeLocalArityTerminalAdmittedConstructionRun public

treeLocalRunToLocalRun :
  ∀ {state : Q2.BoundedSelfReferenceState} →
  TreeLocalArityTerminalAdmittedConstructionRun state →
  Local.LocalArityTerminalAdmittedConstructionRun state
treeLocalRunToLocalRun run =
  Local.local-arity-terminal-admitted-construction-run
    (construction run)
    (treeLocalBuildsLocalAdmission
      (treeLocalAdmission run))
    (allOverheadFits run)
    (machineConstructionAndNextStrict run)

TreeLocalArityTerminalAdmittedStateConstructor : Set₁
TreeLocalArityTerminalAdmittedStateConstructor =
  (state : Q2.BoundedSelfReferenceState) →
  Maybe (TreeLocalArityTerminalAdmittedConstructionRun state)

treeLocalConstructorToLocal :
  TreeLocalArityTerminalAdmittedStateConstructor →
  Local.LocalArityTerminalAdmittedStateConstructor
treeLocalConstructorToLocal constructor state
    with constructor state
... | nothing =
  nothing
... | just run =
  just (treeLocalRunToLocalRun run)

treeLocalConstructorToQ2StepSystem :
  TreeLocalArityTerminalAdmittedStateConstructor →
  Q2.BoundedSelfReferenceStepSystem
treeLocalConstructorToQ2StepSystem constructor =
  Local.localConstructorToQ2StepSystem
    (treeLocalConstructorToLocal constructor)

------------------------------------------------------------------------
-- REGRESSION: zero-variable roots need exactly one structural leaf.
------------------------------------------------------------------------

zeroVariableTree :
  ∀ {root : SAT.BooleanFormula zero}
    {candidate : Candidate.TransitionTableCandidate root}
    (label : Fin (Candidate.stateCount candidate) → Bool) →
  label (Candidate.rootState candidate)
  ≡
  SAT.evaluate root FutureSAT.emptyAssignment →
  TerminalVerificationTree
    candidate
    label
    root
    (Candidate.rootState candidate)
zeroVariableTree label exact =
  terminalLeaf exact

------------------------------------------------------------------------
-- FRONTIER CONSEQUENCE
--
-- Removed from the strongest primitive interface:
--   * full-prefix completeness;
--   * global terminalLabelCorrect.
--
-- Replaced by a finite tree whose leaves are literal structural checks and
-- whose branches follow the candidate's actual transition table.
------------------------------------------------------------------------
