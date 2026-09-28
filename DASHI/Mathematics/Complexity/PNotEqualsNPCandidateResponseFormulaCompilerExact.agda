module DASHI.Mathematics.Complexity.PNotEqualsNPCandidateResponseFormulaCompilerExact where

------------------------------------------------------------------------
-- CANDIDATE-AWARE RESPONSE FORMULA COMPILER
--
-- This owner separates two statements which must not be conflated.
--
--   (1) Harmless executable compiler:
--
--       given candidate code c_D and an input formula phi, run c_D(phi) and
--       emit a Cook formula of the opposite SAT polarity.
--
--   (2) Dangerous same-object equation:
--
--       phi = compile(c_D, phi).
--
-- The compiler itself is ordinary syntax/program plumbing.  The self-equation
-- is already a concrete SATDecisionFailure witness.  Therefore A1 must not
-- silently require this semantic fixed-point equation before the intended
-- width/progress argument.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.PNotEqualsNPDirectSATLowerBoundExact as Direct
import DASHI.Mathematics.Complexity.PNotEqualsNPCandidateActualSelfInstantiationBoundaryExact as Actual

------------------------------------------------------------------------
-- Literal compiler using the executable candidate code, not Direct.decide as
-- an oracle.
------------------------------------------------------------------------

candidateResponseFormula :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost} →
  Actual.CandidateCodeRealization candidate →
  Cook.BooleanFormula →
  Cook.BooleanFormula
candidateResponseFormula code input
    with Actual.CandidateCodeRealization.runCandidateCode
      code
      (Actual.CandidateCodeRealization.candidateCode code)
      input
... | false =
  Cook.excludedMiddleFormula
... | true =
  Direct.contradictionFormula

------------------------------------------------------------------------
-- Exact selection theorems transported through codeDecisionExact.
------------------------------------------------------------------------

candidateRejectsSelectsSatisfiableResponse :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (code : Actual.CandidateCodeRealization candidate)
    (input : Cook.BooleanFormula) →
  Direct.decide candidate input ≡ false →
  candidateResponseFormula code input
  ≡
  Cook.excludedMiddleFormula
candidateRejectsSelectsSatisfiableResponse
    {candidate = candidate}
    code
    input
    rejected
    with
      Actual.CandidateCodeRealization.runCandidateCode
        code
        (Actual.CandidateCodeRealization.candidateCode code)
        input
      |
      Actual.CandidateCodeRealization.codeDecisionExact
        code
        input
... | false | exact =
  refl
... | true | exact =
  impossible (sym exact)
  where
    impossible :
      Direct.decide candidate input ≡ true →
      candidateResponseFormula code input
      ≡
      Cook.excludedMiddleFormula
    impossible decisionTrue
      rewrite rejected in decisionTrue =
      falseNotTrue decisionTrue
      where
        falseNotTrue : false ≡ true → _
        falseNotTrue ()

candidateAcceptsSelectsUnsatisfiableResponse :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (code : Actual.CandidateCodeRealization candidate)
    (input : Cook.BooleanFormula) →
  Direct.decide candidate input ≡ true →
  candidateResponseFormula code input
  ≡
  Direct.contradictionFormula
candidateAcceptsSelectsUnsatisfiableResponse
    {candidate = candidate}
    code
    input
    accepted
    with
      Actual.CandidateCodeRealization.runCandidateCode
        code
        (Actual.CandidateCodeRealization.candidateCode code)
        input
      |
      Actual.CandidateCodeRealization.codeDecisionExact
        code
        input
... | false | exact =
  impossible (sym exact)
  where
    impossible :
      Direct.decide candidate input ≡ false →
      candidateResponseFormula code input
      ≡
      Direct.contradictionFormula
    impossible decisionFalse
      rewrite accepted in decisionFalse =
      trueNotFalse decisionFalse
      where
        trueNotFalse : true ≡ false → _
        trueNotFalse ()
... | true | exact =
  refl

candidateRejectedResponseIsSatisfiable :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (code : Actual.CandidateCodeRealization candidate)
    (input : Cook.BooleanFormula) →
  Direct.decide candidate input ≡ false →
  Cook.Satisfiable
    (candidateResponseFormula code input)
candidateRejectedResponseIsSatisfiable
    code
    input
    rejected =
  subst
    Cook.Satisfiable
    (sym
      (candidateRejectsSelectsSatisfiableResponse
        code input rejected))
    Cook.excludedMiddleFormulaIsSatisfiable

candidateAcceptedResponseIsUnsatisfiable :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (code : Actual.CandidateCodeRealization candidate)
    (input : Cook.BooleanFormula) →
  Direct.decide candidate input ≡ true →
  Cook.Satisfiable
    (candidateResponseFormula code input) →
  ⊥
candidateAcceptedResponseIsUnsatisfiable
    code
    input
    accepted
    satisfiable =
  Direct.contradictionFormulaIsUnsatisfiable
    (subst
      Cook.Satisfiable
      (candidateAcceptsSelectsUnsatisfiableResponse
        code input accepted)
      satisfiable)

------------------------------------------------------------------------
-- FIREWALL: the literal semantic self-equation is already failure strength.
------------------------------------------------------------------------

record CandidateResponseSelfEquation
    {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    (candidate : Direct.PolynomialSATDeciderCandidate cost)
    (code : Actual.CandidateCodeRealization candidate) : Set where
  field
    formula :
      Cook.BooleanFormula

    selfEquation :
      formula
      ≡
      candidateResponseFormula code formula

open CandidateResponseSelfEquation public

candidateResponseSelfEquationGivesFailure :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    {code : Actual.CandidateCodeRealization candidate} →
  CandidateResponseSelfEquation candidate code →
  Direct.SATDecisionFailure candidate
candidateResponseSelfEquationGivesFailure
    {candidate = candidate}
    {code = code}
    fixed
    with Direct.decide candidate (formula fixed)
... | false =
  Direct.falseNegative
    (formula fixed)
    fixedSatisfiable
    refl
  where
    responseSatisfiable :
      Cook.Satisfiable
        (candidateResponseFormula code (formula fixed))
    responseSatisfiable =
      candidateRejectedResponseIsSatisfiable
        code
        (formula fixed)
        refl

    fixedSatisfiable :
      Cook.Satisfiable (formula fixed)
    fixedSatisfiable =
      subst
        Cook.Satisfiable
        (sym (selfEquation fixed))
        responseSatisfiable

... | true =
  Direct.falsePositive
    (formula fixed)
    refl
    fixedUnsatisfiable
  where
    responseUnsatisfiable :
      Cook.Satisfiable
        (candidateResponseFormula code (formula fixed)) →
      ⊥
    responseUnsatisfiable =
      candidateAcceptedResponseIsUnsatisfiable
        code
        (formula fixed)
        refl

    fixedUnsatisfiable :
      Cook.Satisfiable (formula fixed) →
      ⊥
    fixedUnsatisfiable satisfiable =
      responseUnsatisfiable
        (subst
          Cook.Satisfiable
          (selfEquation fixed)
          satisfiable)

------------------------------------------------------------------------
-- Safe A1 compiler packaging.
--
-- This records only code -> formula transformation at an externally supplied
-- input.  It intentionally does NOT assert input = output.
------------------------------------------------------------------------

record CandidateResponseCompilerAt
    {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (code : Actual.CandidateCodeRealization candidate)
    (input : Cook.BooleanFormula) : Set where
  constructor candidate-response-compiler-at
  field
    output :
      Cook.BooleanFormula

    outputExact :
      output
      ≡
      candidateResponseFormula code input

open CandidateResponseCompilerAt public

canonicalCandidateResponseCompilerAt :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (code : Actual.CandidateCodeRealization candidate)
    (input : Cook.BooleanFormula) →
  CandidateResponseCompilerAt code input
canonicalCandidateResponseCompilerAt code input =
  candidate-response-compiler-at
    (candidateResponseFormula code input)
    refl

------------------------------------------------------------------------
-- FRONTIER CONSEQUENCE
--
-- Paid harmlessly:
--
--   c_D + phi -> response formula,
--   with exact opposite-polarity behavior.
--
-- Forbidden as "mere A1 plumbing":
--
--   phi = response(c_D, phi),
--
-- because that equality alone yields SATDecisionFailure.
--
-- Therefore the honest same-object target cannot simply be a semantic formula
-- fixed point of the opposite-SAT compiler.  It must instead identify s_D with
-- an operational self-instantiation/quotation computation whose successful Q1
-- compression is a separate theorem.  That preserves the intended A/B/C split.
------------------------------------------------------------------------
