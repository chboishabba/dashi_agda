module DASHI.Mathematics.Complexity.PNotEqualsNPOppositeSemanticProgramQuotationExact where

------------------------------------------------------------------------
-- OPPOSITE CANDIDATE SELF-APPLICATION + SEMANTIC PROGRAM QUOTATION
--
-- Current structural quotation is injective but tautological.  The correct
-- diagonal target is different:
--
--   quoteProgram p is SAT  iff  run1 p tt = just true.
--
-- Give the finite recursion-theorem primitive opposite semantics:
--
--   primitive(p) = not (D (quoteProgram p)).
--
-- The existing finite fixed-point program p* then satisfies
--
--   run1 p* tt = just (not (D (quoteProgram p*))).
--
-- A semantics-bearing quotation therefore gives
--
--   SAT(quoteProgram p*) iff not D(quoteProgram p*),
--
-- hence a concrete SATDecisionFailure for D.
--
-- This owner proves that implication.  It does NOT assume or manufacture a
-- semantics-bearing quotation.  The remaining constructive wall is precisely
-- to realize this quotation via the repository's concrete Cook--Levin
-- machinery for an executable finite interpreter.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (sym; trans)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.PNotEqualsNPDirectSATLowerBoundExact as Direct
import DASHI.Mathematics.Complexity.PNotEqualsNPCandidateActualSelfInstantiationBoundaryExact as Actual
import DASHI.Mathematics.Complexity.PNotEqualsNPFiniteSelfSpecializingCodeExact as Code

------------------------------------------------------------------------
-- Boolean negation.
------------------------------------------------------------------------

notBool : Bool → Bool
notBool false = true
notBool true = false

notFalse : notBool false ≡ true
notFalse = refl

notTrue : notBool true ≡ false
notTrue = refl

falseNotTrue : false ≡ true → ⊥
falseNotTrue ()

------------------------------------------------------------------------
-- One primitive whose binary behavior flips D on the quotation of the quoted
-- program.
------------------------------------------------------------------------

data OppositeQuotedPrimitive
    {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (code : Actual.CandidateCodeRealization candidate) : Set where
  runOppositeCandidateOnQuote :
    OppositeQuotedPrimitive code

------------------------------------------------------------------------
-- Quotation surface.  This is syntax only; semantic authority is separate.
------------------------------------------------------------------------

record OppositeProgramQuotation
    {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (code : Actual.CandidateCodeRealization candidate) : Set₁ where
  field
    quoteProgram :
      Code.Program (OppositeQuotedPrimitive code) →
      Cook.BooleanFormula

open OppositeProgramQuotation public

------------------------------------------------------------------------
-- Exact primitive/interpreter semantics.
------------------------------------------------------------------------

oppositePrimitiveSemantics :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (code : Actual.CandidateCodeRealization candidate)
    (quotation : OppositeProgramQuotation code) →
  Code.PrimitiveSemantics
    (OppositeQuotedPrimitive code)
    ⊤
    Bool
oppositePrimitiveSemantics code quotation =
  record
    { Code.runPrimitive1 =
        λ primitive input → nothing
    ; Code.runPrimitive2 =
        λ primitive quoted input →
          just
            (notBool
              (Actual.CandidateCodeRealization.runCandidateCode
                code
                (Actual.CandidateCodeRealization.candidateCode code)
                (quoteProgram quotation quoted)))
    }

oppositePrimitiveRunsExact :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (code : Actual.CandidateCodeRealization candidate)
    (quotation : OppositeProgramQuotation code)
    (quoted : Code.Program (OppositeQuotedPrimitive code)) →
  Code.runPrimitive2
      (oppositePrimitiveSemantics code quotation)
      runOppositeCandidateOnQuote
      quoted
      tt
  ≡
  just
    (notBool
      (Direct.decide
        candidate
        (quoteProgram quotation quoted)))
oppositePrimitiveRunsExact
    {candidate = candidate}
    code
    quotation
    quoted
    rewrite
      Actual.CandidateCodeRealization.codeDecisionExact
        code
        (quoteProgram quotation quoted) =
  refl

------------------------------------------------------------------------
-- Literal finite fixed point.
------------------------------------------------------------------------

oppositeFixedPointProgram :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (code : Actual.CandidateCodeRealization candidate) →
  Code.Program (OppositeQuotedPrimitive code)
oppositeFixedPointProgram code =
  Code.primitiveBodyFixedPoint
    runOppositeCandidateOnQuote

oppositeFixedPointRunsExact :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (code : Actual.CandidateCodeRealization candidate)
    (quotation : OppositeProgramQuotation code) →
  Code.run1
      (oppositePrimitiveSemantics code quotation)
      (oppositeFixedPointProgram code)
      tt
  ≡
  just
    (notBool
      (Direct.decide
        candidate
        (quoteProgram quotation
          (oppositeFixedPointProgram code))))
oppositeFixedPointRunsExact
    code
    quotation =
  trans
    (Code.primitiveBodyFixedPointRun
      (oppositePrimitiveSemantics code quotation)
      runOppositeCandidateOnQuote
      tt)
    (oppositePrimitiveRunsExact
      code
      quotation
      (oppositeFixedPointProgram code))

------------------------------------------------------------------------
-- The missing constructive object: a quotation whose SAT semantics agrees
-- with execution truth of the finite program interpreter.
------------------------------------------------------------------------

record SemanticProgramQuotation
    {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (code : Actual.CandidateCodeRealization candidate) : Set₁ where
  field
    quotation : OppositeProgramQuotation code

    trueRunGivesSAT :
      (program : Code.Program (OppositeQuotedPrimitive code)) →
      Code.run1
        (oppositePrimitiveSemantics code quotation)
        program
        tt
      ≡ just true →
      Cook.Satisfiable
        (quoteProgram quotation program)

    satGivesTrueRun :
      (program : Code.Program (OppositeQuotedPrimitive code)) →
      Cook.Satisfiable
        (quoteProgram quotation program) →
      Code.run1
        (oppositePrimitiveSemantics code quotation)
        program
        tt
      ≡ just true

open SemanticProgramQuotation public

------------------------------------------------------------------------
-- Main diagonal theorem: semantic quotation gives one concrete SAT failure.
------------------------------------------------------------------------

semanticQuotationGivesDecisionFailure :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (code : Actual.CandidateCodeRealization candidate) →
  SemanticProgramQuotation code →
  Direct.SATDecisionFailure candidate
semanticQuotationGivesDecisionFailure
    {candidate = candidate}
    code
    semantic
    with
      Direct.decide candidate fixedFormula
... | false =
  Direct.falseNegative
    fixedFormula
    fixedSAT
    refl
  where
    quotation : OppositeProgramQuotation code
    quotation =
      SemanticProgramQuotation.quotation semantic

    fixedProgram : Code.Program (OppositeQuotedPrimitive code)
    fixedProgram =
      oppositeFixedPointProgram code

    fixedFormula : Cook.BooleanFormula
    fixedFormula =
      quoteProgram quotation fixedProgram

    fixedRunTrue :
      Code.run1
        (oppositePrimitiveSemantics code quotation)
        fixedProgram
        tt
      ≡ just true
    fixedRunTrue =
      oppositeFixedPointRunsExact code quotation

    fixedSAT : Cook.Satisfiable fixedFormula
    fixedSAT =
      trueRunGivesSAT semantic
        fixedProgram
        fixedRunTrue

... | true =
  Direct.falsePositive
    fixedFormula
    refl
    fixedUnsatisfiable
  where
    quotation : OppositeProgramQuotation code
    quotation =
      SemanticProgramQuotation.quotation semantic

    fixedProgram : Code.Program (OppositeQuotedPrimitive code)
    fixedProgram =
      oppositeFixedPointProgram code

    fixedFormula : Cook.BooleanFormula
    fixedFormula =
      quoteProgram quotation fixedProgram

    fixedRunFalse :
      Code.run1
        (oppositePrimitiveSemantics code quotation)
        fixedProgram
        tt
      ≡ just false
    fixedRunFalse =
      oppositeFixedPointRunsExact code quotation

    fixedUnsatisfiable : Cook.Satisfiable fixedFormula → ⊥
    fixedUnsatisfiable satisfiable =
      falseNotTrue
        (justInjective
          (trans
            (sym fixedRunFalse)
            (satGivesTrueRun semantic
              fixedProgram
              satisfiable)))
      where
        justInjective :
          ∀ {left right : Bool} →
          just left ≡ just right →
          left ≡ right
        justInjective refl = refl

------------------------------------------------------------------------
-- Universal consequence, conditional ONLY on supplying the semantic quotation
-- for each executable candidate realization.
------------------------------------------------------------------------

record SemanticQuotationProducer
    (cost : PR.PolynomialCostModel Cook.BooleanFormula) : Set₂ where
  field
    candidateCode :
      (candidate : Direct.PolynomialSATDeciderCandidate cost) →
      Actual.CandidateCodeRealization candidate

    semanticQuotation :
      (candidate : Direct.PolynomialSATDeciderCandidate cost) →
      SemanticProgramQuotation
        (candidateCode candidate)

open SemanticQuotationProducer public

semanticQuotationProducerGivesUniversalFailure :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula} →
  SemanticQuotationProducer cost →
  Direct.UniversalPolynomialSATDecisionFailure cost
semanticQuotationProducerGivesUniversalFailure producer candidate =
  semanticQuotationGivesDecisionFailure
    (candidateCode producer candidate)
    (semanticQuotation producer candidate)

------------------------------------------------------------------------
-- FRONTIER CONSEQUENCE
--
-- The logical diagonal is now fully paid once a semantics-bearing quotation is
-- available.  The only surviving constructive theorem is therefore:
--
--   finite opposite interpreter program
--      -> concrete execution/Cook--Levin formula
--      -> SAT iff interpreter returns true,
--
-- with the candidate's executable code and quotation compiler realized by the
-- SAME concrete machine model and with honest polynomial/resource bounds.
--
-- The existing structural quotation cannot fill this field: it is already
-- proved variable-free and tautological.
------------------------------------------------------------------------
