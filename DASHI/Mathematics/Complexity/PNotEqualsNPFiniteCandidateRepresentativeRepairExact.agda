module DASHI.Mathematics.Complexity.PNotEqualsNPFiniteCandidateRepresentativeRepairExact where

------------------------------------------------------------------------
-- REPAIRED FINITE Q1 REPRESENTATIVES
--
-- Raw Shannon restrictions preserve syntax-node count exactly, so they cannot
-- themselves serve as "strictly smaller" representatives.
--
-- Correct separation:
--
--   raw reachable node
--       = provenance / generated-state witness
--
--   evaluator-verified RewriteProgram
--       = semantic reduction certificate
--
--   literal terminal constant of that program
--       = actual strict representative
--
-- This owner reconstructs the strict/closed quotient from exactly that data.
-- No SAT oracle or candidate decision bit is added.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin.Base using (Fin)
open import Data.Nat.Base using (_<_; z≤n; s≤s)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (sym; trans)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.BooleanFormulaSATSelfReductionExact as SAT
import DASHI.Mathematics.Complexity.PNotEqualsNPCookIndexedFormulaBridgeExact as Bridge
import DASHI.Mathematics.Complexity.PNotEqualsNPProgramDescriptionFormulaEmbeddingExact as Size
import DASHI.Mathematics.Complexity.PNotEqualsNPSelfDiagonalRestrictionFamilyExact as Family
import DASHI.Mathematics.Complexity.PNotEqualsNPResourceClosingRestrictionQuotientExact as Quotient
import DASHI.Mathematics.Complexity.PNotEqualsNPTransitionGeneratedRestrictionQuotientExact as Generated
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1FiniteCandidateSemanticAdmissionExact as Candidate
import DASHI.Mathematics.Complexity.PNotEqualsNPAnswerBlindStructuralRewriteMachineExact as Rewrite
import DASHI.Mathematics.Complexity.PNotEqualsNPStrictSemanticRepresentativeQuotientExact as Strict
import DASHI.Mathematics.Complexity.PNotEqualsNPClosedStrictRepresentativeQuotientExact as Closed
import DASHI.Mathematics.Complexity.PNotEqualsNPReachableRewriteGeneratedQ1Exact as Reachable

------------------------------------------------------------------------
-- A rewrite program proves exact satisfiability equivalence with its terminal
-- literal constant.
------------------------------------------------------------------------

rewriteProgramEquivalentToTerminalConstant :
  ∀ {formula : Cook.BooleanFormula}
    (program : Rewrite.RewriteProgram formula) →
  Strict.CookSatisfiabilityEquivalent
    formula
    (Cook.constant
      (Rewrite.rewriteProgramTruth program))
rewriteProgramEquivalentToTerminalConstant
    (Rewrite.halt value) =
  (λ satisfiable → satisfiable)
  ,
  (λ satisfiable → satisfiable)
rewriteProgramEquivalentToTerminalConstant
    (Rewrite.step {before = before} {after = after} rewrite rest) =
  forward
  ,
  backward
  where
    first :
      Strict.CookSatisfiabilityEquivalent
        before
        after
    first =
      Rewrite.rewriteSatisfiabilityEquivalent rewrite

    tail :
      Strict.CookSatisfiabilityEquivalent
        after
        (Cook.constant
          (Rewrite.rewriteProgramTruth rest))
    tail =
      rewriteProgramEquivalentToTerminalConstant rest

    forward :
      Cook.Satisfiable before →
      Cook.Satisfiable
        (Cook.constant
          (Rewrite.rewriteProgramTruth rest))
    forward satisfiable =
      proj₁ tail
        (proj₁ first satisfiable)

    backward :
      Cook.Satisfiable
        (Cook.constant
          (Rewrite.rewriteProgramTruth rest)) →
      Cook.Satisfiable before
    backward satisfiable =
      proj₂ first
        (proj₂ tail satisfiable)

------------------------------------------------------------------------
-- Raw per-state provenance.  There is intentionally NO size-decrease field.
------------------------------------------------------------------------

record RepairedCandidateStateProvenance
    {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (candidate : Candidate.TransitionTableCandidate root)
    (state : Fin (Candidate.stateCount candidate)) : Set₁ where
  constructor repaired-candidate-state-provenance
  field
    currentVariables :
      Nat

    formula :
      SAT.BooleanFormula currentVariables

    derivation :
      Family.RestrictionDerivation root formula

    selectsState :
      Candidate.candidateSelect candidate derivation
      ≡
      state

    rewriteProgram :
      Rewrite.RewriteProgram
        (Bridge.indexedToCook formula)

open RepairedCandidateStateProvenance public

------------------------------------------------------------------------
-- One repaired finite candidate.
--
-- A live root must have room for a one-node strict representative.  Terminal
-- one-node roots should stop rather than request another Q1 construction.
------------------------------------------------------------------------

record RepairedFiniteQ1Candidate
    {rootVariables : Nat}
    (root : SAT.BooleanFormula rootVariables) : Set₁ where
  constructor repaired-finite-q1-candidate
  field
    transitionCandidate :
      Candidate.TransitionTableCandidate root

    stateProvenance :
      (state :
        Fin
          (Candidate.stateCount transitionCandidate)) →
      RepairedCandidateStateProvenance
        transitionCandidate
        state

    rootHasRoomForConstantRepresentative :
      suc zero
      <
      Size.formulaNodeCount
        (Bridge.indexedToCook root)

open RepairedFiniteQ1Candidate public

------------------------------------------------------------------------
-- The semantic representative is the literal terminal constant certified by
-- that state's rewrite program.
------------------------------------------------------------------------

repairedRepresentative :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (candidate : RepairedFiniteQ1Candidate root) →
  Fin
    (Candidate.stateCount
      (transitionCandidate candidate)) →
  Cook.BooleanFormula
repairedRepresentative candidate state =
  Cook.constant
    (Rewrite.rewriteProgramTruth
      (rewriteProgram
        (stateProvenance candidate state)))

------------------------------------------------------------------------
-- Every reachable current formula is equivalent to its repaired representative.
------------------------------------------------------------------------

repairedRepresentativeEquivalent :
  ∀ {rootVariables currentVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (candidate : RepairedFiniteQ1Candidate root)
    (congruence :
      Candidate.GeneratedSemanticCongruence
        (transitionCandidate candidate))
    {current : SAT.BooleanFormula currentVariables}
    (derivation : Family.RestrictionDerivation root current) →
  Strict.CookSatisfiabilityEquivalent
    (Bridge.indexedToCook current)
    (repairedRepresentative
      candidate
      (Candidate.candidateSelect
        (transitionCandidate candidate)
        derivation))
repairedRepresentativeEquivalent
    candidate
    congruence
    derivation =
  compose
    currentToRaw
    rawToConstant
  where
    transition :
      Candidate.TransitionTableCandidate root
    transition =
      transitionCandidate candidate

    state :
      Fin (Candidate.stateCount transition)
    state =
      Candidate.candidateSelect transition derivation

    source :
      RepairedCandidateStateProvenance transition state
    source =
      stateProvenance candidate state

    sameState :
      Candidate.candidateSelect transition derivation
      ≡
      Candidate.candidateSelect transition
        (RepairedCandidateStateProvenance.derivation source)
    sameState =
      sym
        (RepairedCandidateStateProvenance.selectsState source)

    currentToRawIndexed :
      Quotient.SatisfiabilityEquivalent
        current
        (RepairedCandidateStateProvenance.formula source)
    currentToRawIndexed =
      congruence
        derivation
        (RepairedCandidateStateProvenance.derivation source)
        sameState

    currentToRaw :
      Strict.CookSatisfiabilityEquivalent
        (Bridge.indexedToCook current)
        (Bridge.indexedToCook
          (RepairedCandidateStateProvenance.formula source))
    currentToRaw =
      Reachable.indexedEquivalentToCookEquivalent
        currentToRawIndexed

    rawToConstant :
      Strict.CookSatisfiabilityEquivalent
        (Bridge.indexedToCook
          (RepairedCandidateStateProvenance.formula source))
        (repairedRepresentative candidate state)
    rawToConstant =
      rewriteProgramEquivalentToTerminalConstant
        (RepairedCandidateStateProvenance.rewriteProgram source)

    compose :
      ∀ {left middle right : Cook.BooleanFormula} →
      Strict.CookSatisfiabilityEquivalent left middle →
      Strict.CookSatisfiabilityEquivalent middle right →
      Strict.CookSatisfiabilityEquivalent left right
    compose leftMiddle middleRight =
      (λ leftSat →
        proj₁ middleRight
          (proj₁ leftMiddle leftSat))
      ,
      (λ rightSat →
        proj₂ leftMiddle
          (proj₂ middleRight rightSat))

------------------------------------------------------------------------
-- Every repaired representative has exactly one node and is therefore strict.
------------------------------------------------------------------------

repairedRepresentativeStrictlySmaller :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (candidate : RepairedFiniteQ1Candidate root)
    (state :
      Fin
        (Candidate.stateCount
          (transitionCandidate candidate))) →
  Size.formulaNodeCount
      (repairedRepresentative candidate state)
  <
  Size.formulaNodeCount
      (Bridge.indexedToCook root)
repairedRepresentativeStrictlySmaller candidate state =
  rootHasRoomForConstantRepresentative candidate

------------------------------------------------------------------------
-- Compile to the existing strict quotient.
------------------------------------------------------------------------

repairedToStrictSemanticRepresentativeQuotient :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (candidate : RepairedFiniteQ1Candidate root) →
  Candidate.GeneratedSemanticCongruence
    (transitionCandidate candidate) →
  Strict.StrictSemanticRepresentativeQuotient root
repairedToStrictSemanticRepresentativeQuotient
    candidate
    congruence =
  Strict.strict-semantic-representative-quotient
    quotient
    (repairedRepresentative candidate)
    (repairedRepresentativeEquivalent
      candidate
      congruence)
    (repairedRepresentativeStrictlySmaller
      candidate)
  where
    generated :
      Generated.TransitionGeneratedRestrictionQuotient root
    generated =
      Candidate.admitTransitionTableCandidate
        (transitionCandidate candidate)
        congruence

    quotient :
      Quotient.RestrictionSemanticQuotient root
    quotient =
      Generated.toRestrictionSemanticQuotient
        generated

------------------------------------------------------------------------
-- Since the repaired representatives are already literal constants, their
-- structural closure chains are terminal by construction.
------------------------------------------------------------------------

repairedToClosedStrictRepresentativeQuotient :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (candidate : RepairedFiniteQ1Candidate root) →
  Candidate.GeneratedSemanticCongruence
    (transitionCandidate candidate) →
  Closed.ClosedStrictRepresentativeQuotient root
repairedToClosedStrictRepresentativeQuotient
    candidate
    congruence =
  Closed.closed-strict-representative-quotient
    (repairedToStrictSemanticRepresentativeQuotient
      candidate
      congruence)
    (λ state →
      Closed.terminal
        (Rewrite.rewriteProgramTruth
          (rewriteProgram
            (stateProvenance candidate state))))

------------------------------------------------------------------------
-- FRONTIER CONSEQUENCE
--
-- The previous vacuity is removed without relaxing semantic authority:
--
--   * generated-state data are still finite;
--   * provenance is still an actual Shannon descendant;
--   * state truth still comes only from evaluator-valid rewrite syntax;
--   * strictness now applies to the terminal semantic representative, where it
--     is actually true.
--
-- The remaining hard obligations are now meaningful again:
-- construct the transition table + one normalizing rewrite program per reached
-- state, derive arity/terminal semantic admission, and fit the resulting table,
-- construction trace and next authority inside the recursive budget.
------------------------------------------------------------------------
