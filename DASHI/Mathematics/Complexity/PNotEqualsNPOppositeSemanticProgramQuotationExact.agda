module DASHI.Mathematics.Complexity.PNotEqualsNPOppositeSemanticProgramQuotationExact where

------------------------------------------------------------------------
-- OPPOSITE CANDIDATE SELF-APPLICATION + SEMANTIC PROGRAM QUOTATION
--
-- Current structural quotation is injective but tautological. The correct
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
-- This owner proves that implication. It does NOT assume or manufacture a
-- semantics-bearing quotation. The remaining constructive wall is precisely
-- to realize this quotation via the repository's concrete Cook--Levin
-- machinery for an executable finite interpreter.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Maybe.Base using (just; nothing)
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (sym; trans)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.PNotEqualsNPDirectSATLowerBoundExact as Direct
import DASHI.Mathematics.Complexity.PNotEqualsNPCandidateActualSelfInstantiationBoundaryExact as Actual
import DASHI.Mathematics.Complexity.PNotEqualsNPFiniteSelfSpecializingCodeExact as Code

notBool : Bool → Bool
notBool false = true
notBool true = false

falseNotTrue : false ≡ true → ⊥
falseNotTrue ()

data OppositeQuotedPrimitive
    {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (code : Actual.CandidateCodeRealization candidate) : Set where
  runOppositeCandidateOnQuote : OppositeQuotedPrimitive code

record OppositeProgramQuotation
    {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (code : Actual.CandidateCodeRealization candidate) : Set₁ where
  field
    quoteProgram :
      Code.Program (OppositeQuotedPrimitive code) →
      Cook.BooleanFormula

open OppositeProgramQuotation public

oppositePrimitiveSemantics :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (code : Actual.CandidateCodeRealization candidate)
    (quotation : OppositeProgramQuotation code) →
  Code.PrimitiveSemantics (OppositeQuotedPrimitive code) ⊤ Bool
oppositePrimitiveSemantics code quotation = record
  { Code.runPrimitive1 = λ primitive input → nothing
  ; Code.runPrimitive2 = λ primitive quoted input →
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
  ≡ just
      (notBool
        (Direct.decide candidate
          (quoteProgram quotation quoted)))
oppositePrimitiveRunsExact {candidate = candidate} code quotation quoted
    rewrite
      Actual.CandidateCodeRealization.codeDecisionExact
        code
        (quoteProgram quotation quoted) =
  refl

oppositeFixedPointProgram :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (code : Actual.CandidateCodeRealization candidate) →
  Code.Program (OppositeQuotedPrimitive code)
oppositeFixedPointProgram code =
  Code.primitiveBodyFixedPoint runOppositeCandidateOnQuote

oppositeFixedPointRunsExact :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (code : Actual.CandidateCodeRealization candidate)
    (quotation : OppositeProgramQuotation code) →
  Code.run1
      (oppositePrimitiveSemantics code quotation)
      (oppositeFixedPointProgram code)
      tt
  ≡ just
      (notBool
        (Direct.decide candidate
          (quoteProgram quotation
            (oppositeFixedPointProgram code))))
oppositeFixedPointRunsExact code quotation =
  trans
    (Code.primitiveBodyFixedPointRun
      (oppositePrimitiveSemantics code quotation)
      runOppositeCandidateOnQuote
      tt)
    (oppositePrimitiveRunsExact
      code
      quotation
      (oppositeFixedPointProgram code))

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
      Cook.Satisfiable (quoteProgram quotation program)

    satGivesTrueRun :
      (program : Code.Program (OppositeQuotedPrimitive code)) →
      Cook.Satisfiable (quoteProgram quotation program) →
      Code.run1
        (oppositePrimitiveSemantics code quotation)
        program
        tt
      ≡ just true

open SemanticProgramQuotation public

------------------------------------------------------------------------
-- Named fixed objects avoid any branch-local `with` scoping ambiguity.
------------------------------------------------------------------------

semanticFixedProgram :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (code : Actual.CandidateCodeRealization candidate) →
  Code.Program (OppositeQuotedPrimitive code)
semanticFixedProgram = oppositeFixedPointProgram

semanticFixedFormula :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (code : Actual.CandidateCodeRealization candidate) →
  SemanticProgramQuotation code →
  Cook.BooleanFormula
semanticFixedFormula code semantic =
  quoteProgram
    (quotation semantic)
    (semanticFixedProgram code)

semanticFixedRunExact :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (code : Actual.CandidateCodeRealization candidate)
    (semantic : SemanticProgramQuotation code) →
  Code.run1
      (oppositePrimitiveSemantics code (quotation semantic))
      (semanticFixedProgram code)
      tt
  ≡ just
      (notBool
        (Direct.decide candidate
          (semanticFixedFormula code semantic)))
semanticFixedRunExact code semantic =
  oppositeFixedPointRunsExact code (quotation semantic)

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
    with Direct.decide candidate (semanticFixedFormula code semantic)
... | false =
  Direct.falseNegative
    (semanticFixedFormula code semantic)
    fixedSAT
    refl
  where
    fixedRunTrue :
      Code.run1
        (oppositePrimitiveSemantics code (quotation semantic))
        (semanticFixedProgram code)
        tt
      ≡ just true
    fixedRunTrue =
      semanticFixedRunExact code semantic

    fixedSAT : Cook.Satisfiable (semanticFixedFormula code semantic)
    fixedSAT =
      trueRunGivesSAT semantic
        (semanticFixedProgram code)
        fixedRunTrue

... | true =
  Direct.falsePositive
    (semanticFixedFormula code semantic)
    refl
    fixedUnsatisfiable
  where
    fixedRunFalse :
      Code.run1
        (oppositePrimitiveSemantics code (quotation semantic))
        (semanticFixedProgram code)
        tt
      ≡ just false
    fixedRunFalse =
      semanticFixedRunExact code semantic

    justInjective :
      ∀ {left right : Bool} →
      just left ≡ just right →
      left ≡ right
    justInjective refl = refl

    fixedUnsatisfiable :
      Cook.Satisfiable (semanticFixedFormula code semantic) → ⊥
    fixedUnsatisfiable satisfiable =
      falseNotTrue
        (justInjective
          (trans
            (sym fixedRunFalse)
            (satGivesTrueRun semantic
              (semanticFixedProgram code)
              satisfiable)))

record SemanticQuotationProducer
    (cost : PR.PolynomialCostModel Cook.BooleanFormula) : Set₂ where
  field
    candidateCode :
      (candidate : Direct.PolynomialSATDeciderCandidate cost) →
      Actual.CandidateCodeRealization candidate

    semanticQuotation :
      (candidate : Direct.PolynomialSATDeciderCandidate cost) →
      SemanticProgramQuotation (candidateCode candidate)

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
-- The logical diagonal is fully paid once a semantics-bearing quotation is
-- available. The only surviving constructive theorem is therefore:
--
--   finite opposite interpreter program
--      -> concrete execution/Cook--Levin formula
--      -> SAT iff interpreter returns true,
--
-- with the candidate's executable code and quotation compiler realized by the
-- SAME concrete machine model and with honest polynomial/resource bounds.
------------------------------------------------------------------------
