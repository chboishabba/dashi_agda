module DASHI.Mathematics.Complexity.PNotEqualsNPCandidateQuotedSelfApplicationExact where

------------------------------------------------------------------------
-- CANDIDATE-CODE SELF-APPLICATION THROUGH LITERAL PROGRAM QUOTATION
--
-- The remaining A1 representation seam is a quotation map
--
--   finite Program -> Cook.BooleanFormula.
--
-- Given ANY such quotation, this owner builds a finite primitive whose binary
-- semantics really consumes its quoted program:
--
--   runCandidateOnQuote q
--      = runCandidateCode c_D (quoteProgram q).
--
-- Applying the repository's existing literal finite specialization/diagonal
-- construction to that primitive yields an actual fixed program p*_D with
--
--   run1 p*_D tt
--      = just (decide D (quoteProgram p*_D)).
--
-- This is genuine candidate-aware self-application.  It contains no SAT
-- correctness, satisfiability, opposite-polarity, or decision-failure premise.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.Maybe.Base using (Maybe; nothing; just)
open import Relation.Binary.PropositionalEquality using (trans)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.PNotEqualsNPDirectSATLowerBoundExact as Direct
import DASHI.Mathematics.Complexity.PNotEqualsNPFiniteSelfSpecializingCodeExact as Code
import DASHI.Mathematics.Complexity.PNotEqualsNPPartialKleeneFixedPointExact as Kleene
import DASHI.Mathematics.Complexity.PNotEqualsNPCandidateActualSelfInstantiationBoundaryExact as Actual

------------------------------------------------------------------------
-- Quotation interface.
--
-- No semantic law is hidden here: it is only finite syntax -> Cook syntax.
-- A later concrete implementation can quote constructor tags and embedded
-- candidate-code bits using the repository's existing finite bit/formula
-- encoders.
------------------------------------------------------------------------

record ProgramFormulaQuotation (Primitive : Set) : Set₁ where
  field
    quoteProgram :
      Code.Program Primitive →
      Cook.BooleanFormula

open ProgramFormulaQuotation public

------------------------------------------------------------------------
-- One primitive: evaluate D on the literal quotation of the quoted program.
------------------------------------------------------------------------

data CandidateQuotedPrimitive
    {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (code : Actual.CandidateCodeRealization candidate) : Set where
  runCandidateOnQuote :
    CandidateQuotedPrimitive code

------------------------------------------------------------------------
-- Candidate-aware binary semantics.
------------------------------------------------------------------------

candidateQuotedPrimitiveSemantics :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (code : Actual.CandidateCodeRealization candidate)
    (quotation :
      ProgramFormulaQuotation
        (CandidateQuotedPrimitive code)) →
  Code.PrimitiveSemantics
    (CandidateQuotedPrimitive code)
    ⊤
    Bool
candidateQuotedPrimitiveSemantics code quotation =
  record
    { Code.runPrimitive1 =
        λ primitive input → nothing
    ; Code.runPrimitive2 =
        λ primitive quoted input →
          just
            (Actual.CandidateCodeRealization.runCandidateCode
              code
              (Actual.CandidateCodeRealization.candidateCode code)
              (quoteProgram quotation quoted))
    }

candidateQuotedPrimitiveRunsExactDecision :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (code : Actual.CandidateCodeRealization candidate)
    (quotation :
      ProgramFormulaQuotation
        (CandidateQuotedPrimitive code))
    (quoted :
      Code.Program
        (CandidateQuotedPrimitive code)) →
  Code.runPrimitive2
      (candidateQuotedPrimitiveSemantics code quotation)
      runCandidateOnQuote
      quoted
      tt
  ≡
  just
    (Direct.decide
      candidate
      (quoteProgram quotation quoted))
candidateQuotedPrimitiveRunsExactDecision
    code
    quotation
    quoted
    rewrite
      Actual.CandidateCodeRealization.codeDecisionExact
        code
        (quoteProgram quotation quoted) =
  refl

------------------------------------------------------------------------
-- Literal fixed point from the repository's finite code calculus.
------------------------------------------------------------------------

candidateQuotedFixedPointProgram :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (code : Actual.CandidateCodeRealization candidate) →
  Code.Program
    (CandidateQuotedPrimitive code)
candidateQuotedFixedPointProgram code =
  Code.primitiveBodyFixedPoint
    runCandidateOnQuote

candidateQuotedFixedPointFormula :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (code : Actual.CandidateCodeRealization candidate) →
  ProgramFormulaQuotation
    (CandidateQuotedPrimitive code) →
  Cook.BooleanFormula
candidateQuotedFixedPointFormula code quotation =
  quoteProgram quotation
    (candidateQuotedFixedPointProgram code)

------------------------------------------------------------------------
-- Exact operational self-application theorem.
------------------------------------------------------------------------

candidateQuotedFixedPointRunsCandidateOnOwnQuotation :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (code : Actual.CandidateCodeRealization candidate)
    (quotation :
      ProgramFormulaQuotation
        (CandidateQuotedPrimitive code)) →
  Code.run1
      (candidateQuotedPrimitiveSemantics code quotation)
      (candidateQuotedFixedPointProgram code)
      tt
  ≡
  just
    (Direct.decide
      candidate
      (candidateQuotedFixedPointFormula
        code
        quotation))
candidateQuotedFixedPointRunsCandidateOnOwnQuotation
    code
    quotation =
  trans
    (Code.primitiveBodyFixedPointRun
      (candidateQuotedPrimitiveSemantics code quotation)
      runCandidateOnQuote
      tt)
    (candidateQuotedPrimitiveRunsExactDecision
      code
      quotation
      (candidateQuotedFixedPointProgram code))

------------------------------------------------------------------------
-- Same-object operational root package.
--
-- The Boolean root is literally the quotation of the actual self-specialized
-- finite program whose execution invokes D on that same quotation.
------------------------------------------------------------------------

record CandidateQuotedSelfApplication
    {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    (candidate : Direct.PolynomialSATDeciderCandidate cost)
    (code : Actual.CandidateCodeRealization candidate) : Set₁ where
  field
    quotation :
      ProgramFormulaQuotation
        (CandidateQuotedPrimitive code)

    fixedProgram :
      Code.Program
        (CandidateQuotedPrimitive code)

    fixedProgramExact :
      fixedProgram
      ≡
      candidateQuotedFixedPointProgram code

    rootFormula :
      Cook.BooleanFormula

    rootFormulaExact :
      rootFormula
      ≡
      quoteProgram quotation fixedProgram

    executionExact :
      Code.run1
        (candidateQuotedPrimitiveSemantics
          code quotation)
        fixedProgram
        tt
      ≡
      just
        (Direct.decide candidate rootFormula)

open CandidateQuotedSelfApplication public

canonicalCandidateQuotedSelfApplication :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (code : Actual.CandidateCodeRealization candidate)
    (quotation :
      ProgramFormulaQuotation
        (CandidateQuotedPrimitive code)) →
  CandidateQuotedSelfApplication candidate code
canonicalCandidateQuotedSelfApplication
    {candidate = candidate}
    code
    quotation =
  record
    { quotation =
        quotation
    ; fixedProgram =
        candidateQuotedFixedPointProgram code
    ; fixedProgramExact =
        refl
    ; rootFormula =
        candidateQuotedFixedPointFormula code quotation
    ; rootFormulaExact =
        refl
    ; executionExact =
        candidateQuotedFixedPointRunsCandidateOnOwnQuotation
          code quotation
    }

------------------------------------------------------------------------
-- Strength firewall.
--
-- This package proves only:
--
--   p*_D evaluates D on quote(p*_D).
--
-- It DOES NOT prove:
--
--   SAT(quote(p*_D)) iff D rejects quote(p*_D),
--   quote(p*_D) = oppositeResponse(D, quote(p*_D)),
--   constructor(s_D) != nothing.
--
-- Therefore this operational same-object self-application is strictly below
-- the already-proved SAT-failure-strength semantic response self-equation.
------------------------------------------------------------------------

data CandidateQuotedSelfApplicationStatus : Set where
  candidateCodeConsumed : CandidateQuotedSelfApplicationStatus
  quotedProgramConsumed : CandidateQuotedSelfApplicationStatus
  literalFiniteFixedPointPaid : CandidateQuotedSelfApplicationStatus
  ownQuotationDecisionExact : CandidateQuotedSelfApplicationStatus
  satPolaritySemanticsPaid : CandidateQuotedSelfApplicationStatus
  firstStepProgressPaid : CandidateQuotedSelfApplicationStatus

currentCandidateQuotedSelfApplicationStatus :
  CandidateQuotedSelfApplicationStatus
currentCandidateQuotedSelfApplicationStatus =
  ownQuotationDecisionExact

------------------------------------------------------------------------
-- FRONTIER
--
-- A1 is now reduced to a representation theorem:
--
--   implement ProgramFormulaQuotation concretely,
--   bind rootFormula to Q2.currentFormula(s_D),
--   charge candidate-code + quotation/rebinding size exactly.
--
-- The candidate-aware self-application computation itself is paid.
--
-- Only after that exact Q2 root exists should B ask whether the direct-DP
-- constructor must make one successful step.
------------------------------------------------------------------------
