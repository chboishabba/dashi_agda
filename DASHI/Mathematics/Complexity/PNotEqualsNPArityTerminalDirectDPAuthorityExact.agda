module DASHI.Mathematics.Complexity.PNotEqualsNPArityTerminalDirectDPAuthorityExact where

------------------------------------------------------------------------
-- ARITY/TERMINAL ADMISSION -> DIRECT QUOTIENT-DP AUTHORITY
--
-- The repaired representative audit reveals that per-state strict
-- representatives are unnecessary once the transition table already carries:
--
--   * exact remaining arity for every selected state;
--   * correct structural truth labels at arity zero.
--
-- Those are precisely the inputs required by the existing quotient dynamic
-- program.  This owner therefore compiles them directly:
--
--   transition candidate + arity/terminal admission
--       -> generated semantic congruence
--       -> legacy quotient
--       -> exact terminal labelling
--       -> depth-by-state dynamic program
--       -> exact root SAT bit
--       -> one-node Cook constant authority.
--
-- No raw restriction is claimed smaller, no per-state RewriteProgram is
-- required, and no hypothetical SAT decider supplies a label.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat.Base using (_<_)
open import Relation.Binary.PropositionalEquality using (sym; trans)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.BooleanFormulaSATSelfReductionExact as SAT
import DASHI.Mathematics.Complexity.BooleanFormulaFiniteSATDecisionExact as Finite
import DASHI.Mathematics.Complexity.SATDecisionToWitnessSelfReductionExact as Search
import DASHI.Mathematics.Complexity.PNotEqualsNPCookIndexedFormulaBridgeExact as Bridge
import DASHI.Mathematics.Complexity.PNotEqualsNPProgramDescriptionFormulaEmbeddingExact as Size
import DASHI.Mathematics.Complexity.PNotEqualsNPSelfDiagonalRestrictionFamilyExact as Family
import DASHI.Mathematics.Complexity.PNotEqualsNPResourceClosingRestrictionQuotientExact as Quotient
import DASHI.Mathematics.Complexity.PNotEqualsNPTransitionGeneratedRestrictionQuotientExact as Generated
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1FiniteCandidateSemanticAdmissionExact as Candidate
import DASHI.Mathematics.Complexity.PNotEqualsNPArityTrackedTerminalSemanticAdmissionExact as ArityTerminal
import DASHI.Mathematics.Complexity.PNotEqualsNPRestrictionQuotientDynamicProgrammingExact as DP
import DASHI.Mathematics.Complexity.PNotEqualsNPClosedStrictRepresentativeQuotientExact as Closed
import DASHI.Mathematics.Complexity.PNotEqualsNPStrictSemanticRepresentativeQuotientExact as Strict

falseNotTrue : false ≡ true → ⊥
falseNotTrue ()

------------------------------------------------------------------------
-- At arity zero, the finite SAT decider is literally evaluation of the unique
-- empty assignment.
------------------------------------------------------------------------

zeroVariableFiniteDecisionExact :
  (formula : SAT.BooleanFormula zero) →
  Finite.decideFiniteSATBool formula
  ≡
  SAT.evaluate formula Finite.emptyAssignment
zeroVariableFiniteDecisionExact formula
    with SAT.evaluate formula Finite.emptyAssignment
... | false =
  refl
... | true =
  refl

------------------------------------------------------------------------
-- Candidate + local admission -> exact generated/legacy quotient.
------------------------------------------------------------------------

admittedGenerated :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (candidate : Candidate.TransitionTableCandidate root) →
  ArityTerminal.ArityTrackedTerminalAdmission candidate →
  Generated.TransitionGeneratedRestrictionQuotient root
admittedGenerated candidate admission =
  Candidate.admitTransitionTableCandidate
    candidate
    (ArityTerminal.arityTerminalAdmissionBuildsSemanticCongruence
      admission)

admittedQuotient :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (candidate : Candidate.TransitionTableCandidate root) →
  ArityTerminal.ArityTrackedTerminalAdmission candidate →
  Quotient.RestrictionSemanticQuotient root
admittedQuotient candidate admission =
  Generated.toRestrictionSemanticQuotient
    (admittedGenerated candidate admission)

------------------------------------------------------------------------
-- Arity-zero labels from the local admission are already the terminal labels
-- required by the quotient DP.
------------------------------------------------------------------------

arityTerminalLabels :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (candidate : Candidate.TransitionTableCandidate root)
    (admission :
      ArityTerminal.ArityTrackedTerminalAdmission candidate) →
  DP.TerminalStateLabelling
    (admittedQuotient candidate admission)
    Closed.finiteSATOracle
arityTerminalLabels candidate admission =
  DP.terminal-state-labelling
    (ArityTerminal.terminalLabel admission)
    terminalCorrect
  where
    terminalCorrect :
      ∀ {terminal : SAT.BooleanFormula zero}
        (derivation :
          Family.RestrictionDerivation root terminal) →
      ArityTerminal.terminalLabel admission
        (Quotient.classify
          (admittedQuotient candidate admission)
          derivation)
      ≡
      Search.decide
        Closed.finiteSATOracle
        terminal
    terminalCorrect {terminal} derivation =
      trans
        (ArityTerminal.terminalLabelCorrect
          admission
          derivation)
        (sym
          (zeroVariableFiniteDecisionExact terminal))

------------------------------------------------------------------------
-- Exact root truth bit computed by the depth/state dynamic program.
------------------------------------------------------------------------

arityTerminalRootTruth :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (candidate : Candidate.TransitionTableCandidate root)
    (admission :
      ArityTerminal.ArityTrackedTerminalAdmission candidate) →
  Bool
arityTerminalRootTruth
    {rootVariables}
    candidate
    admission =
  DP.quotientTruthAtDepth
    (admittedQuotient candidate admission)
    (arityTerminalLabels candidate admission)
    rootVariables
    (Quotient.classify
      (admittedQuotient candidate admission)
      Family.restrictionRoot)

arityTerminalRootTruthExact :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (candidate : Candidate.TransitionTableCandidate root)
    (admission :
      ArityTerminal.ArityTrackedTerminalAdmission candidate) →
  arityTerminalRootTruth candidate admission
  ≡
  Finite.decideFiniteSATBool root
arityTerminalRootTruthExact candidate admission =
  DP.quotientTruthComputesRootDecision
    (admittedQuotient candidate admission)
    Closed.finiteSATOracle
    (arityTerminalLabels candidate admission)

------------------------------------------------------------------------
-- One-node exact semantic authority.
------------------------------------------------------------------------

arityTerminalDPAuthority :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables} →
  (candidate : Candidate.TransitionTableCandidate root) →
  ArityTerminal.ArityTrackedTerminalAdmission candidate →
  Cook.BooleanFormula
arityTerminalDPAuthority candidate admission =
  Cook.constant
    (arityTerminalRootTruth candidate admission)

rootSatisfiableGivesDPAuthoritySatisfiable :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (candidate : Candidate.TransitionTableCandidate root)
    (admission :
      ArityTerminal.ArityTrackedTerminalAdmission candidate) →
  SAT.Satisfying root →
  Cook.Satisfiable
    (arityTerminalDPAuthority candidate admission)
rootSatisfiableGivesDPAuthoritySatisfiable
    {root = root}
    candidate
    admission
    rootSat =
  Cook.satisfyingAssignment
    (λ index → false)
    truthIsTrue
  where
    decisionTrue :
      Finite.decideFiniteSATBool root ≡ true
    decisionTrue =
      Finite.decideFiniteSATBoolComplete
        root
        rootSat

    truthIsTrue :
      arityTerminalRootTruth candidate admission
      ≡
      true
    truthIsTrue =
      trans
        (arityTerminalRootTruthExact
          candidate
          admission)
        decisionTrue

dpAuthoritySatisfiableGivesRootSatisfying :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (candidate : Candidate.TransitionTableCandidate root)
    (admission :
      ArityTerminal.ArityTrackedTerminalAdmission candidate) →
  Cook.Satisfiable
    (arityTerminalDPAuthority candidate admission) →
  SAT.Satisfying root
dpAuthoritySatisfiableGivesRootSatisfying
    {root = root}
    candidate
    admission
    authoritySat =
  Finite.decideFiniteSATBoolSound
    root
    decisionTrue
  where
    truthIsTrue :
      arityTerminalRootTruth candidate admission
      ≡
      true
    truthIsTrue =
      Cook.evaluatesTrue authoritySat

    decisionTrue :
      Finite.decideFiniteSATBool root
      ≡
      true
    decisionTrue =
      trans
        (sym
          (arityTerminalRootTruthExact
            candidate
            admission))
        truthIsTrue

arityTerminalDPAuthorityEquivalent :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (candidate : Candidate.TransitionTableCandidate root)
    (admission :
      ArityTerminal.ArityTrackedTerminalAdmission candidate) →
  Strict.CookSatisfiabilityEquivalent
    (Bridge.indexedToCook root)
    (arityTerminalDPAuthority candidate admission)
arityTerminalDPAuthorityEquivalent
    {root = root}
    candidate
    admission =
  forward
  ,
  backward
  where
    forward :
      Cook.Satisfiable
        (Bridge.indexedToCook root) →
      Cook.Satisfiable
        (arityTerminalDPAuthority candidate admission)
    forward rootCook =
      rootSatisfiableGivesDPAuthoritySatisfiable
        candidate
        admission
        (Bridge.cookSatisfiableIndexedFormulaGivesIndexedSatisfying
          root
          rootCook)

    backward :
      Cook.Satisfiable
        (arityTerminalDPAuthority candidate admission) →
      Cook.Satisfiable
        (Bridge.indexedToCook root)
    backward authoritySat =
      Bridge.indexedSatisfyingGivesCookSatisfiable
        root
        (dpAuthoritySatisfiableGivesRootSatisfying
          candidate
          admission
          authoritySat)

------------------------------------------------------------------------
-- The authority itself is exactly one syntax node.
------------------------------------------------------------------------

arityTerminalDPAuthorityNodeCount :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (candidate : Candidate.TransitionTableCandidate root)
    (admission :
      ArityTerminal.ArityTrackedTerminalAdmission candidate) →
  Size.formulaNodeCount
    (arityTerminalDPAuthority candidate admission)
  ≡
  suc zero
arityTerminalDPAuthorityNodeCount candidate admission =
  refl

arityTerminalDPAuthorityStrictlySmaller :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (candidate : Candidate.TransitionTableCandidate root)
    (admission :
      ArityTerminal.ArityTrackedTerminalAdmission candidate) →
  suc zero
  <
  Size.formulaNodeCount
    (Bridge.indexedToCook root) →
  Size.formulaNodeCount
    (arityTerminalDPAuthority candidate admission)
  <
  Size.formulaNodeCount
    (Bridge.indexedToCook root)
arityTerminalDPAuthorityStrictlySmaller
    candidate
    admission
    rootHasRoom =
  rootHasRoom

------------------------------------------------------------------------
-- Exact represented evaluation cost already owned by the quotient-DP module.
------------------------------------------------------------------------

arityTerminalEvaluationCellCount :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (candidate : Candidate.TransitionTableCandidate root)
    (admission :
      ArityTerminal.ArityTrackedTerminalAdmission candidate) →
  Nat
arityTerminalEvaluationCellCount candidate admission =
  DP.quotientEvaluationCellCount
    (admittedQuotient candidate admission)

------------------------------------------------------------------------
-- FRONTIER CONSEQUENCE
--
-- The Q1 object is now minimal and non-vacuous:
--
--   finite transition table
--   + local arity tracking
--   + literal terminal labels
--   + charged DP table/construction.
--
-- Per-state strict representatives and rewrite-to-constant programs are not
-- needed for semantic closure.  The remaining hard theorem is exactly the
-- quantitative one: construct this admitted table cheaply enough that
--
--   quotient graph + (n+1)*stateCount + construction + next-state overhead
--
-- fits the self-reference descent budget.  Residual-width lower bounds attack
-- that stateCount directly.
------------------------------------------------------------------------
