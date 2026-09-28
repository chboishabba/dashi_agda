module DASHI.Mathematics.Complexity.PNotEqualsNPQ1TerminalSemanticsDecisionFailureExact where

------------------------------------------------------------------------
-- Q1 TERMINAL SEMANTICS IS EXACTLY A CONCRETE SAT DECISION FAILURE
--
-- The concrete finite-code Q2 executor has already been proved to collapse all
-- terminating quoted programs to one canonical terminal formula A.
--
-- Therefore the Q1 semantic premise
--
--   D(A)=false -> SAT(A)
--   SAT(A)      -> D(A)=false
--
-- is not merely a precursor to a later diagonal contradiction.  By case split
-- on D(A), it immediately exhibits either:
--
--   * a false positive, when D(A)=true; or
--   * a false negative, when D(A)=false.
--
-- Conversely, every concrete SATDecisionFailure can be represented by a
-- trivial all-stop Q2 system whose terminal formula is exactly the failure
-- formula.  Hence the current finite-code Q1 terminal package is extensionally
-- equivalent to the direct failure object already present on the Clay-critical
-- surface.
--
-- This recuts the frontier: recurrence/width machinery may constrain HOW a
-- failure-producing package is constructed, but Q1OppositeSATTerminalSemantics
-- itself already CONTAINS the decision failure.  It cannot be derived from
-- exact SAT DP without paying the lower-bound theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe.Base using (nothing; just)
open import Data.Product using (Σ; _,_; _×_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.PNotEqualsNPDirectSATLowerBoundExact as Direct
import DASHI.Mathematics.Complexity.PNotEqualsNPBoundedSelfReferenceWellFoundedExact as Q2
import DASHI.Mathematics.Complexity.PNotEqualsNPFiniteSelfSpecializingCodeExact as Code
import DASHI.Mathematics.Complexity.PNotEqualsNPFiniteCodeQ2ExecutionRealizationExact as Exec
import DASHI.Mathematics.Complexity.PNotEqualsNPPartialKleeneFixedPointExact as Kleene
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1FiniteCodeClayClosureExact as ClayClosure
import DASHI.Mathematics.Complexity.PNotEqualsNPQ2TerminatingQuoteCollapseExact as Collapse
import DASHI.Mathematics.Complexity.PNotEqualsNPInitialStateImageUnconstrainedExact as Initial

trueNotFalse : true ≡ false → ⊥
trueNotFalse ()

falseNotTrue : false ≡ true → ⊥
falseNotTrue ()

------------------------------------------------------------------------
-- One terminal opposite-SAT certificate is already one concrete error.
------------------------------------------------------------------------

terminalOppositeSATGivesDecisionFailure :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    {stepSystem : Q2.BoundedSelfReferenceStepSystem}
    {initial : Q2.BoundedSelfReferenceState} →
  Collapse.TerminalOppositeSAT
    candidate
    stepSystem
    initial →
  Direct.SATDecisionFailure candidate
terminalOppositeSATGivesDecisionFailure
    {candidate = candidate}
    {stepSystem = stepSystem}
    {initial = initial}
    terminalSemantics
    with Direct.decide candidate terminalFormula
... | true =
  Direct.falsePositive
    terminalFormula
    refl
    unsatisfiable
  where
    terminalFormula :
      Cook.BooleanFormula
    terminalFormula =
      Exec.canonicalTerminalFormula
        stepSystem
        initial

    unsatisfiable :
      Cook.Satisfiable terminalFormula →
      ⊥
    unsatisfiable satisfiable =
      trueNotFalse
        (proj₂ terminalSemantics satisfiable)

... | false =
  Direct.falseNegative
    terminalFormula
    satisfiable
    refl
  where
    terminalFormula :
      Cook.BooleanFormula
    terminalFormula =
      Exec.canonicalTerminalFormula
        stepSystem
        initial

    satisfiable :
      Cook.Satisfiable terminalFormula
    satisfiable =
      proj₁ terminalSemantics refl

q1TerminalSemanticsGivesDecisionFailure :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (stepSystem : Q2.BoundedSelfReferenceStepSystem)
    (initial : Q2.BoundedSelfReferenceState) →
  ClayClosure.Q1OppositeSATTerminalSemantics
    candidate
    stepSystem
    initial →
  Direct.SATDecisionFailure candidate
q1TerminalSemanticsGivesDecisionFailure
    stepSystem
    initial
    semantics =
  terminalOppositeSATGivesDecisionFailure
    (Collapse.q1AllQuotesGivesTerminalOppositeSAT
      _
      stepSystem
      initial
      semantics)

------------------------------------------------------------------------
-- Trivial stop system used for the converse.
------------------------------------------------------------------------

allStopSystem :
  Q2.BoundedSelfReferenceStepSystem
allStopSystem =
  Q2.bounded-self-reference-step-system
    (λ state → nothing)
    strictlyDecreases
  where
    strictlyDecreases :
      (state nextState : Q2.BoundedSelfReferenceState) →
      nothing ≡ just nextState →
      Q2.recursiveMeasure nextState
      <
      Q2.recursiveMeasure state
    strictlyDecreases state nextState ()

allStopTerminalFormulaExact :
  (formula : Cook.BooleanFormula) →
  Exec.canonicalTerminalFormula
      allStopSystem
      (Initial.initialStateForFormula formula)
  ≡
  formula
allStopTerminalFormulaExact formula =
  refl

------------------------------------------------------------------------
-- Transport helpers for satisfiability and candidate decisions.
------------------------------------------------------------------------

transportSatisfiable :
  ∀ {left right : Cook.BooleanFormula} →
  left ≡ right →
  Cook.Satisfiable left →
  Cook.Satisfiable right
transportSatisfiable refl witness =
  witness

transportDecision :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    (candidate : Direct.PolynomialSATDeciderCandidate cost)
    {left right : Cook.BooleanFormula} →
  left ≡ right →
  Direct.decide candidate left
  ≡
  Direct.decide candidate right
transportDecision candidate equality =
  cong (Direct.decide candidate) equality

------------------------------------------------------------------------
-- Every concrete failure yields terminal opposite-SAT semantics for the
-- all-stop system.
------------------------------------------------------------------------

failureGivesAllStopTerminalOppositeSAT :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost} →
  Direct.SATDecisionFailure candidate →
  Σ Cook.BooleanFormula
    (λ formula →
      Collapse.TerminalOppositeSAT
        candidate
        allStopSystem
        (Initial.initialStateForFormula formula))
failureGivesAllStopTerminalOppositeSAT
    {candidate = candidate}
    (Direct.falseNegative formula satisfiable rejected) =
  formula
  ,
  satisfiableIfRejected
  ,
  rejectedIfSatisfiable
  where
    terminalExact :
      Exec.canonicalTerminalFormula
          allStopSystem
          (Initial.initialStateForFormula formula)
      ≡
      formula
    terminalExact =
      allStopTerminalFormulaExact formula

    satisfiableTerminal :
      Cook.Satisfiable
        (Exec.canonicalTerminalFormula
          allStopSystem
          (Initial.initialStateForFormula formula))
    satisfiableTerminal =
      transportSatisfiable
        (sym terminalExact)
        satisfiable

    satisfiableIfRejected :
      Direct.decide candidate
        (Exec.canonicalTerminalFormula
          allStopSystem
          (Initial.initialStateForFormula formula))
      ≡ false →
      Cook.Satisfiable
        (Exec.canonicalTerminalFormula
          allStopSystem
          (Initial.initialStateForFormula formula))
    satisfiableIfRejected terminalRejected =
      satisfiableTerminal

    rejectedIfSatisfiable :
      Cook.Satisfiable
        (Exec.canonicalTerminalFormula
          allStopSystem
          (Initial.initialStateForFormula formula)) →
      Direct.decide candidate
        (Exec.canonicalTerminalFormula
          allStopSystem
          (Initial.initialStateForFormula formula))
      ≡ false
    rejectedIfSatisfiable terminalSat =
      trans
        (transportDecision
          candidate
          terminalExact)
        rejected

failureGivesAllStopTerminalOppositeSAT
    {candidate = candidate}
    (Direct.falsePositive formula accepted unsatisfiable) =
  formula
  ,
  satisfiableIfRejected
  ,
  rejectedIfSatisfiable
  where
    terminalExact :
      Exec.canonicalTerminalFormula
          allStopSystem
          (Initial.initialStateForFormula formula)
      ≡
      formula
    terminalExact =
      allStopTerminalFormulaExact formula

    terminalDecisionAccepted :
      Direct.decide candidate
        (Exec.canonicalTerminalFormula
          allStopSystem
          (Initial.initialStateForFormula formula))
      ≡ true
    terminalDecisionAccepted =
      trans
        (transportDecision
          candidate
          terminalExact)
        accepted

    terminalUnsatisfiable :
      Cook.Satisfiable
        (Exec.canonicalTerminalFormula
          allStopSystem
          (Initial.initialStateForFormula formula)) →
      ⊥
    terminalUnsatisfiable terminalSat =
      unsatisfiable
        (transportSatisfiable
          terminalExact
          terminalSat)

    satisfiableIfRejected :
      Direct.decide candidate
        (Exec.canonicalTerminalFormula
          allStopSystem
          (Initial.initialStateForFormula formula))
      ≡ false →
      Cook.Satisfiable
        (Exec.canonicalTerminalFormula
          allStopSystem
          (Initial.initialStateForFormula formula))
    satisfiableIfRejected terminalRejected =
      ⊥-elim
        (trueNotFalse
          (trans
            (sym terminalDecisionAccepted)
            terminalRejected))

    rejectedIfSatisfiable :
      Cook.Satisfiable
        (Exec.canonicalTerminalFormula
          allStopSystem
          (Initial.initialStateForFormula formula)) →
      Direct.decide candidate
        (Exec.canonicalTerminalFormula
          allStopSystem
          (Initial.initialStateForFormula formula))
      ≡ false
    rejectedIfSatisfiable terminalSat =
      ⊥-elim
        (terminalUnsatisfiable terminalSat)

------------------------------------------------------------------------
-- Recover the full all-quotes Q1 premise using the already-proved quote
-- collapse equivalence.
------------------------------------------------------------------------

failureGivesAllStopQ1TerminalSemantics :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost} →
  Direct.SATDecisionFailure candidate →
  Σ Cook.BooleanFormula
    (λ formula →
      ClayClosure.Q1OppositeSATTerminalSemantics
        candidate
        allStopSystem
        (Initial.initialStateForFormula formula))
failureGivesAllStopQ1TerminalSemantics
    {candidate = candidate}
    failure
    with failureGivesAllStopTerminalOppositeSAT failure
... | formula , terminalSemantics =
  formula
  ,
  Collapse.terminalOppositeSATGivesQ1AllQuotes
    candidate
    allStopSystem
    (Initial.initialStateForFormula formula)
    terminalSemantics

------------------------------------------------------------------------
-- Exact package equivalence.
------------------------------------------------------------------------

CandidateQ1TerminalPackage :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula} →
  Direct.PolynomialSATDeciderCandidate cost →
  Set₁
CandidateQ1TerminalPackage candidate =
  Σ Q2.BoundedSelfReferenceStepSystem
    (λ stepSystem →
      Σ Q2.BoundedSelfReferenceState
        (λ initial →
          ClayClosure.Q1OppositeSATTerminalSemantics
            candidate
            stepSystem
            initial))

q1TerminalPackageGivesDecisionFailure :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost} →
  CandidateQ1TerminalPackage candidate →
  Direct.SATDecisionFailure candidate
q1TerminalPackageGivesDecisionFailure
    (stepSystem , initial , semantics) =
  q1TerminalSemanticsGivesDecisionFailure
    stepSystem
    initial
    semantics

decisionFailureGivesQ1TerminalPackage :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost} →
  Direct.SATDecisionFailure candidate →
  CandidateQ1TerminalPackage candidate
decisionFailureGivesQ1TerminalPackage
    {candidate = candidate}
    failure
    with failureGivesAllStopQ1TerminalSemantics failure
... | formula , semantics =
  allStopSystem
  ,
  Initial.initialStateForFormula formula
  ,
  semantics

------------------------------------------------------------------------
-- FRONTIER CONSEQUENCE
--
-- For the current concrete finite-code executor:
--
--   CandidateQ1TerminalPackage(candidate)
--      <-> SATDecisionFailure(candidate).
--
-- Thus terminal-semantics construction is not an easier intermediate theorem.
-- It IS the direct lower-bound witness, merely repackaged through a terminating
-- Q2 system.
--
-- Width/recurrence machinery remains useful only if it yields the decision
-- failure without assuming Q1OppositeSATTerminalSemantics.  The missing live
-- theorem must couple candidate D to a demanded pre-first-step construction or
-- produce a collision/failure directly.
------------------------------------------------------------------------
