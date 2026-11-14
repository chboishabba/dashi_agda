module DASHI.Mathematics.Complexity.PNotEqualsNPFixedStandardOppositeQuotationExact where

------------------------------------------------------------------------
-- ONE FINITE-PRESENTED STANDARD TM PAYS THE FIXED OPPOSITE QUOTATION
--
-- The previous fixed concrete realization still carried a total deterministic
-- successor on arbitrary concrete rows.  The repository already has a cleaner
-- conventional deterministic semantics: finite-presented StandardSingleTapeTM
-- plus exact standard<->concrete run transport and guarded acceptance iff.
--
-- This owner therefore makes the remaining diagonal execution obligation:
--
--   one finite standard program + one guarded input + one exact T-step run
--   + final-control-bit = not D(its own guarded Cook formula).
--
-- Existing language equivalence and Cook--Levin then derive SAT iff the fixed
-- abstract opposite computation returns true.  No total malformed-row executor
-- or separate concrete deterministic successor is required.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Maybe.Base using (just)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.PNotEqualsNPDirectSATLowerBoundExact as Direct
import DASHI.Mathematics.Complexity.PNotEqualsNPCandidateActualSelfInstantiationBoundaryExact as Actual
import DASHI.Mathematics.Complexity.PNotEqualsNPOppositeSemanticProgramQuotationExact as Opposite
import DASHI.Mathematics.Complexity.PNotEqualsNPFixedOppositeSemanticQuotationExact as Fixed
import DASHI.Mathematics.Complexity.PNotEqualsNPStandardFiniteCandidateCodeExact as Candidate

import DASHI.Mathematics.Complexity.StandardSingleTapeMachineExact as Standard
import DASHI.Mathematics.Complexity.StandardFiniteTapePresentationExact as Presented
import DASHI.Mathematics.Complexity.ConcreteTapeStandardRunExact as StandardRun
import DASHI.Mathematics.Complexity.ConcreteTapeStandardLanguageEquivalenceExact as Language
import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeCanonicalCellBitsExact as Canonical
import DASHI.Mathematics.Complexity.ConcreteTapeRuleSelectorExact as Selector
import DASHI.Mathematics.Complexity.ConcreteTapeInputInitialRowExact as Input
import DASHI.Mathematics.Complexity.ConcreteTapeCookLevinExactBudgetIff as Exact
import DASHI.Mathematics.Complexity.ConcreteTapeCookLevinCookFormulaExact as CookLevin

------------------------------------------------------------------------
-- Fixed finite program data.
------------------------------------------------------------------------

record FixedStandardOppositeMachine
    {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (code : Actual.CandidateCodeRealization candidate) : Set₂ where
  field
    presentation : Presented.FinitePresentedStandardTM

    stateCoverage :
      Canonical.EnumerationCoverage
        (Presented.finiteState presentation)

    symbolCoverage :
      Canonical.EnumerationCoverage
        (Presented.finiteSymbol presentation)

    nonemptyRules :
      Selector.NonemptyRuleTable
        (Presented.finitePresentedStandardToConcrete presentation)

    input :
      Input.InputWord
        (Presented.finitePresentedStandardToConcrete presentation)

    steps : Agda.Builtin.Nat.Nat

open FixedStandardOppositeMachine public

fixedConcreteMachine :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    {code : Actual.CandidateCodeRealization candidate} →
  FixedStandardOppositeMachine code →
  Local.ConcreteTapeMachine
fixedConcreteMachine fixed =
  Presented.finitePresentedStandardToConcrete
    (presentation fixed)

fixedCookFormula :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    {code : Actual.CandidateCodeRealization candidate} →
  FixedStandardOppositeMachine code →
  Cook.BooleanFormula
fixedCookFormula fixed =
  CookLevin.guardedCookFormula
    (stateCoverage fixed)
    (symbolCoverage fixed)
    (nonemptyRules fixed)
    (input fixed)
    (steps fixed)

------------------------------------------------------------------------
-- One exact standard execution and the singular opposite endpoint equation.
------------------------------------------------------------------------

record FixedStandardOppositeEndpointRealization
    {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (code : Actual.CandidateCodeRealization candidate) : Set₂ where
  field
    fixed : FixedStandardOppositeMachine code

    finish :
      Standard.StandardConfiguration
        (Presented.finitePresentedStandardMachine
          (presentation fixed))

    execution :
      StandardRun.StandardExactRun
        (Presented.finitePresentedStandardMachine
          (presentation fixed))
        (steps fixed)
        (Language.guardedStandardStart
          (input fixed)
          (steps fixed))
        finish

    endpointDecisionExact :
      Local.decideEqual
        (Presented.finiteState (presentation fixed))
        (Standard.state finish)
        (Presented.acceptingState (presentation fixed))
      ≡
      Opposite.notBool
        (Direct.decide candidate (fixedCookFormula fixed))

open FixedStandardOppositeEndpointRealization public

------------------------------------------------------------------------
-- Standard final-control decision <-> standard accepting endpoint.
------------------------------------------------------------------------

endpointTrueGivesStandardAccepting :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    {code : Actual.CandidateCodeRealization candidate}
    (realization : FixedStandardOppositeEndpointRealization code) →
  Local.decideEqual
      (Presented.finiteState (presentation (fixed realization)))
      (Standard.state (finish realization))
      (Presented.acceptingState (presentation (fixed realization)))
    ≡ true →
  Standard.standardAccepting (finish realization)
endpointTrueGivesStandardAccepting realization endpointTrue =
  Local.decideEqualSound
    (Presented.finiteState (presentation (fixed realization)))
    endpointTrue

standardAcceptingGivesEndpointTrue :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    {code : Actual.CandidateCodeRealization candidate}
    (realization : FixedStandardOppositeEndpointRealization code) →
  Standard.standardAccepting (finish realization) →
  Local.decideEqual
      (Presented.finiteState (presentation (fixed realization)))
      (Standard.state (finish realization))
      (Presented.acceptingState (presentation (fixed realization)))
    ≡ true
standardAcceptingGivesEndpointTrue realization accepting
    rewrite accepting =
  Local.decideEqualRefl
    (Presented.finiteState (presentation (fixed realization)))
    (Presented.acceptingState (presentation (fixed realization)))

------------------------------------------------------------------------
-- Fixed abstract run true -> exact concrete accepting run.
------------------------------------------------------------------------

fixedRunTrueGivesExactBudgetRun :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    {code : Actual.CandidateCodeRealization candidate}
    (realization : FixedStandardOppositeEndpointRealization code) →
  Fixed.fixedRun code (fixedCookFormula (fixed realization)) ≡ just true →
  Exact.ExactBudgetAcceptingRun
    (input (fixed realization))
    (steps (fixed realization))
fixedRunTrueGivesExactBudgetRun
    {candidate = candidate}
    {code = code}
    realization
    fixedTrue
    with Language.guardedStandardToConcrete
      (Presented.finitePresentedStandardToConcrete_dispatchUnique
        (presentation (fixed realization)))
      standardAccepts
... | concrete = record
  { Exact.rows = Language.rows concrete
  ; Exact.finish = Language.finish concrete
  ; Exact.certificate = Language.certificate concrete
  ; Exact.exactLength = Language.exactLength concrete
  }
  where
    ownFormula : Cook.BooleanFormula
    ownFormula = fixedCookFormula (fixed realization)

    oppositeTrue :
      Opposite.notBool (Direct.decide candidate ownFormula) ≡ true
    oppositeTrue =
      Candidate.justInjective
        (trans
          (sym (Fixed.fixedRunExact code ownFormula))
          fixedTrue)

    endpointTrue :
      Local.decideEqual
        (Presented.finiteState (presentation (fixed realization)))
        (Standard.state (finish realization))
        (Presented.acceptingState (presentation (fixed realization)))
      ≡ true
    endpointTrue =
      trans (endpointDecisionExact realization) oppositeTrue

    standardAccepts :
      Language.GuardedStandardAcceptsIn
        (fixedConcreteMachine (fixed realization))
        (input (fixed realization))
        (steps (fixed realization))
    standardAccepts = record
      { Language.finish = finish realization
      ; Language.run = execution realization
      ; Language.accepting =
          endpointTrueGivesStandardAccepting realization endpointTrue
      }

------------------------------------------------------------------------
-- Exact concrete accepting run -> fixed abstract run true.
------------------------------------------------------------------------

exactBudgetRunGivesFixedRunTrue :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    {code : Actual.CandidateCodeRealization candidate}
    (realization : FixedStandardOppositeEndpointRealization code) →
  Exact.ExactBudgetAcceptingRun
    (input (fixed realization))
    (steps (fixed realization)) →
  Fixed.fixedRun code (fixedCookFormula (fixed realization)) ≡ just true
exactBudgetRunGivesFixedRunTrue
    {candidate = candidate}
    {code = code}
    realization exact =
  trans
    (Fixed.fixedRunExact code ownFormula)
    (cong just oppositeTrue)
  where
    ownFormula : Cook.BooleanFormula
    ownFormula = fixedCookFormula (fixed realization)

    concreteAccepts :
      Language.GuardedConcreteAcceptsIn
        (fixedConcreteMachine (fixed realization))
        (input (fixed realization))
        (steps (fixed realization))
    concreteAccepts = record
      { Language.rows = Exact.rows exact
      ; Language.finish = Exact.finish exact
      ; Language.certificate = Exact.certificate exact
      ; Language.exactLength = Exact.exactLength exact
      }

    projected :
      Language.GuardedStandardAcceptsIn
        (fixedConcreteMachine (fixed realization))
        (input (fixed realization))
        (steps (fixed realization))
    projected =
      Language.guardedConcreteToStandard
        (Presented.finitePresentedStandardToConcrete_dispatchUnique
          (presentation (fixed realization)))
        concreteAccepts

    endpointExact :
      Language.finish projected ≡ finish realization
    endpointExact =
      Candidate.standardExactRunUniqueFinish
        (Language.run projected)
        (execution realization)

    declaredAccepting :
      Standard.standardAccepting (finish realization)
    declaredAccepting =
      trans
        (cong Standard.state (sym endpointExact))
        (Language.accepting projected)

    endpointTrue :
      Local.decideEqual
        (Presented.finiteState (presentation (fixed realization)))
        (Standard.state (finish realization))
        (Presented.acceptingState (presentation (fixed realization)))
      ≡ true
    endpointTrue =
      standardAcceptingGivesEndpointTrue realization declaredAccepting

    oppositeTrue :
      Opposite.notBool (Direct.decide candidate ownFormula) ≡ true
    oppositeTrue =
      trans
        (sym (endpointDecisionExact realization))
        endpointTrue

------------------------------------------------------------------------
-- Existing Cook--Levin iff compiles the endpoint realization to the minimal
-- fixed semantic quotation, hence directly to a SATDecisionFailure.
------------------------------------------------------------------------

standardEndpointToFixedSemanticQuotation :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    {code : Actual.CandidateCodeRealization candidate} →
  FixedStandardOppositeEndpointRealization code →
  Fixed.FixedSemanticQuotation code
standardEndpointToFixedSemanticQuotation realization = record
  { Fixed.formula = fixedCookFormula (fixed realization)
  ; Fixed.trueRunGivesSAT =
      λ fixedTrue →
        CookLevin.exactBudgetRunToCookSatisfiable
          (stateCoverage (fixed realization))
          (symbolCoverage (fixed realization))
          (nonemptyRules (fixed realization))
          (input (fixed realization))
          (steps (fixed realization))
          (fixedRunTrueGivesExactBudgetRun realization fixedTrue)
  ; Fixed.satGivesTrueRun =
      λ satisfiable →
        exactBudgetRunGivesFixedRunTrue
          realization
          (CookLevin.cookSatisfiableToExactBudgetRun
            (stateCoverage (fixed realization))
            (symbolCoverage (fixed realization))
            (nonemptyRules (fixed realization))
            (input (fixed realization))
            (steps (fixed realization))
            satisfiable)
  }

standardEndpointRealizationGivesDecisionFailure :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (code : Actual.CandidateCodeRealization candidate) →
  FixedStandardOppositeEndpointRealization code →
  Direct.SATDecisionFailure candidate
standardEndpointRealizationGivesDecisionFailure code realization =
  Fixed.fixedSemanticQuotationGivesDecisionFailure
    code
    (standardEndpointToFixedSemanticQuotation realization)

------------------------------------------------------------------------
-- FRONTIER CONSEQUENCE
--
-- The diagonal no longer needs a special concrete deterministic execution API.
-- Its one surviving execution theorem is entirely conventional:
--
--   finite-presented standard TM M_D
--   + guarded input x_D
--   + exact T_D-step standard run
--   + finalAcceptBit = not D(CL(M_D,x_D,T_D)).
--
-- Existing exact standard/concrete acceptance equivalence and Cook--Levin then
-- close all semantic directions automatically.
------------------------------------------------------------------------
