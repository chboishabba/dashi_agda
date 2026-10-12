module DASHI.Mathematics.Complexity.PNotEqualsNPStandardFiniteCandidateCodeExact where

------------------------------------------------------------------------
-- POLYNOMIAL SAT CANDIDATE AS ONE FINITE-PRESENTED STANDARD TM
--
-- The existing concrete/standard lane already proves:
--   * finite rule-table standard syntax <-> deterministic ConcreteTapeMachine;
--   * exact T-step run transport in both directions;
--   * guarded-input acceptance iff at the same T;
--   * exact step-clock identity and linear first-match overhead.
--
-- Therefore candidate coverage should be stated on the conventional finite
-- standard machine, not by requiring a total successor on malformed concrete
-- rows.  This owner binds one PolynomialSATDeciderCandidate to that finite
-- program, its genuine finite-enumeration coverage, guarded input encoder,
-- exact clocked standard execution and literal final-control decision bit.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Maybe.Base using (just)
open import Relation.Binary.PropositionalEquality using (sym; trans; cong)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.PNotEqualsNPDirectSATLowerBoundExact as Direct
import DASHI.Mathematics.Complexity.PNotEqualsNPCandidateActualSelfInstantiationBoundaryExact as Actual
import DASHI.Mathematics.Complexity.PNotEqualsNPConcreteTapeProgramCodeExact as ProgramCode
import DASHI.Mathematics.Complexity.StandardSingleTapeMachineExact as Standard
import DASHI.Mathematics.Complexity.StandardFiniteTapePresentationExact as Presented
import DASHI.Mathematics.Complexity.ConcreteTapeStandardRunExact as StandardRun
import DASHI.Mathematics.Complexity.ConcreteTapeStandardLanguageEquivalenceExact as Language

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeCanonicalCellBitsExact as Canonical
import DASHI.Mathematics.Complexity.ConcreteTapeInputInitialRowExact as Input
import DASHI.Mathematics.Complexity.ConcreteTapeCookLevinExactBudgetIff as Exact
import DASHI.Mathematics.Complexity.FixedWidthTruthTableCNFExact as CNF

------------------------------------------------------------------------
-- Functional standard execution has a unique endpoint at each exact length.
------------------------------------------------------------------------

justInjective :
  ∀ {A : Set} {left right : A} →
  just left ≡ just right →
  left ≡ right
justInjective refl = refl

standardExactRunUniqueFinish :
  ∀ {State Symbol : Set}
    {machine : Standard.StandardSingleTapeMachine State Symbol}
    {steps : Nat}
    {start leftFinish rightFinish : Standard.StandardConfiguration machine} →
  StandardRun.StandardExactRun machine steps start leftFinish →
  StandardRun.StandardExactRun machine steps start rightFinish →
  leftFinish ≡ rightFinish
standardExactRunUniqueFinish StandardRun.standardRunDone StandardRun.standardRunDone =
  refl
standardExactRunUniqueFinish
    (StandardRun.standardRunStep leftEdge leftRest)
    (StandardRun.standardRunStep rightEdge rightRest)
    with justInjective (trans (sym leftEdge) rightEdge)
... | refl =
  standardExactRunUniqueFinish leftRest rightRest

------------------------------------------------------------------------
-- One finite-presented standard implementation of the extensional candidate.
------------------------------------------------------------------------

record StandardFiniteCandidateCode
    {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    (candidate : Direct.PolynomialSATDeciderCandidate cost) : Set₂ where
  field
    presentation : Presented.FinitePresentedStandardTM

    -- FiniteEnumeration.complete is intentionally weaker than actual list
    -- membership in this repository.  Static bit quotation needs these exact
    -- genuine-coverage witnesses.
    stateCoverage :
      Canonical.EnumerationCoverage
        (Presented.finiteState presentation)

    symbolCoverage :
      Canonical.EnumerationCoverage
        (Presented.finiteSymbol presentation)

    encodeFormula :
      Cook.BooleanFormula →
      Input.InputWord
        (Presented.finitePresentedStandardToConcrete presentation)

    exactSteps : Cook.BooleanFormula → Nat

    finish :
      (formula : Cook.BooleanFormula) →
      Standard.StandardConfiguration
        (Presented.finitePresentedStandardMachine presentation)

    execution :
      (formula : Cook.BooleanFormula) →
      StandardRun.StandardExactRun
        (Presented.finitePresentedStandardMachine presentation)
        (exactSteps formula)
        (Language.guardedStandardStart
          (encodeFormula formula)
          (exactSteps formula))
        (finish formula)

    decisionExact :
      (formula : Cook.BooleanFormula) →
      Local.decideEqual
        (Presented.finiteState presentation)
        (Standard.state (finish formula))
        (Presented.acceptingState presentation)
      ≡ Direct.decide candidate formula

open StandardFiniteCandidateCode public

candidateConcreteMachine :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost} →
  StandardFiniteCandidateCode candidate →
  Local.ConcreteTapeMachine
candidateConcreteMachine standard =
  Presented.finitePresentedStandardToConcrete
    (presentation standard)

candidateStateCoverage :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (standard : StandardFiniteCandidateCode candidate) →
  Canonical.EnumerationCoverage
    (Local.finiteState (candidateConcreteMachine standard))
candidateStateCoverage standard =
  stateCoverage standard

candidateSymbolCoverage :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (standard : StandardFiniteCandidateCode candidate) →
  Canonical.EnumerationCoverage
    (Local.finiteSymbol (candidateConcreteMachine standard))
candidateSymbolCoverage standard =
  symbolCoverage standard

------------------------------------------------------------------------
-- Literal candidate code = fixed-width static bits of the SAME rule table.
------------------------------------------------------------------------

candidateProgramBits :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (standard : StandardFiniteCandidateCode candidate) →
  CNF.Bits (ProgramCode.StaticProgramBitsWidth (candidateConcreteMachine standard))
candidateProgramBits standard =
  ProgramCode.encodeStaticProgram
    (candidateConcreteMachine standard)
    (candidateStateCoverage standard)
    (candidateSymbolCoverage standard)

candidateProgramBitSize :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost} →
  StandardFiniteCandidateCode candidate → Nat
candidateProgramBitSize standard =
  ProgramCode.StaticProgramBitsWidth (candidateConcreteMachine standard)

standardCandidateToCodeRealization :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost} →
  StandardFiniteCandidateCode candidate →
  Actual.CandidateCodeRealization candidate
standardCandidateToCodeRealization standard = record
  { Actual.CandidateCode =
      CNF.Bits (candidateProgramBitSize standard)
  ; Actual.candidateCode = candidateProgramBits standard
  ; Actual.runCandidateCode =
      λ bits formula →
        Local.decideEqual
          (Presented.finiteState (presentation standard))
          (Standard.state (finish standard formula))
          (Presented.acceptingState (presentation standard))
  ; Actual.codeDecisionExact = decisionExact standard
  ; Actual.codeSize = λ bits → candidateProgramBitSize standard
  }

------------------------------------------------------------------------
-- Endpoint decision lemmas.
------------------------------------------------------------------------

standardDecisionTrueGivesAccepting :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (standard : StandardFiniteCandidateCode candidate)
    (formula : Cook.BooleanFormula) →
  Direct.decide candidate formula ≡ true →
  Standard.standardAccepting (finish standard formula)
standardDecisionTrueGivesAccepting standard formula candidateTrue =
  Local.decideEqualSound
    (Presented.finiteState (presentation standard))
    (trans (decisionExact standard formula) candidateTrue)

standardAcceptingGivesDecisionTrue :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (standard : StandardFiniteCandidateCode candidate)
    (formula : Cook.BooleanFormula) →
  Standard.standardAccepting (finish standard formula) →
  Direct.decide candidate formula ≡ true
standardAcceptingGivesDecisionTrue standard formula accepting =
  trans
    (sym (decisionExact standard formula))
    endpointTrue
  where
    endpointTrue :
      Local.decideEqual
        (Presented.finiteState (presentation standard))
        (Standard.state (finish standard formula))
        (Presented.acceptingState (presentation standard))
      ≡ true
    endpointTrue
      rewrite accepting =
      Local.decideEqualRefl
        (Presented.finiteState (presentation standard))
        (Presented.acceptingState (presentation standard))

------------------------------------------------------------------------
-- Candidate=true -> exact concrete accepting run at the SAME T.
------------------------------------------------------------------------

candidateTrueGivesExactBudgetRun :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (standard : StandardFiniteCandidateCode candidate)
    (formula : Cook.BooleanFormula) →
  Direct.decide candidate formula ≡ true →
  Exact.ExactBudgetAcceptingRun
    (encodeFormula standard formula)
    (exactSteps standard formula)
candidateTrueGivesExactBudgetRun standard formula candidateTrue
    with Language.guardedStandardToConcrete
      (Presented.finitePresentedStandardToConcrete_dispatchUnique
        (presentation standard))
      standardAccepts
... | concrete = record
  { Exact.rows = Language.rows concrete
  ; Exact.finish = Language.finish concrete
  ; Exact.certificate = Language.certificate concrete
  ; Exact.exactLength = Language.exactLength concrete
  }
  where
    standardAccepts :
      Language.GuardedStandardAcceptsIn
        (candidateConcreteMachine standard)
        (encodeFormula standard formula)
        (exactSteps standard formula)
    standardAccepts = record
      { Language.finish = finish standard formula
      ; Language.run = execution standard formula
      ; Language.accepting =
          standardDecisionTrueGivesAccepting standard formula candidateTrue
      }

------------------------------------------------------------------------
-- Any exact concrete accepting run -> candidate=true.
--
-- The concrete accepting run projects to a standard accepting run. Since
-- standardNext is functional, its endpoint equals the candidate's declared
-- deterministic endpoint at the same exact step count.
------------------------------------------------------------------------

exactBudgetRunGivesCandidateTrue :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (standard : StandardFiniteCandidateCode candidate)
    (formula : Cook.BooleanFormula) →
  Exact.ExactBudgetAcceptingRun
    (encodeFormula standard formula)
    (exactSteps standard formula) →
  Direct.decide candidate formula ≡ true
exactBudgetRunGivesCandidateTrue standard formula exact =
  standardAcceptingGivesDecisionTrue
    standard formula deterministicAccepting
  where
    concreteAccepts :
      Language.GuardedConcreteAcceptsIn
        (candidateConcreteMachine standard)
        (encodeFormula standard formula)
        (exactSteps standard formula)
    concreteAccepts = record
      { Language.rows = Exact.rows exact
      ; Language.finish = Exact.finish exact
      ; Language.certificate = Exact.certificate exact
      ; Language.exactLength = Exact.exactLength exact
      }

    projected :
      Language.GuardedStandardAcceptsIn
        (candidateConcreteMachine standard)
        (encodeFormula standard formula)
        (exactSteps standard formula)
    projected =
      Language.guardedConcreteToStandard
        (Presented.finitePresentedStandardToConcrete_dispatchUnique
          (presentation standard))
        concreteAccepts

    endpointExact :
      Language.finish projected ≡ finish standard formula
    endpointExact =
      standardExactRunUniqueFinish
        (Language.run projected)
        (execution standard formula)

    deterministicAccepting :
      Standard.standardAccepting (finish standard formula)
    deterministicAccepting =
      trans
        (cong Standard.state (sym endpointExact))
        (Language.accepting projected)

------------------------------------------------------------------------
-- FRONTIER CONSEQUENCE
--
-- For a finitely presented conventional deterministic single-tape machine,
-- the candidate-code and Cook--Levin semantic interfaces are now automatic:
-- no total successor on malformed concrete rows is needed.
--
-- The only remaining MODEL-COVERAGE obligation is therefore the conventional
-- one: identify the selected notion of polynomial-time decider with finite-
-- presented standard machines carrying a polynomial clock. The already-paid
-- concrete/standard exact simulations preserve the run and acceptance once
-- such a standard machine is supplied.
------------------------------------------------------------------------
