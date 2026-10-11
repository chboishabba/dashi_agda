module DASHI.Mathematics.Complexity.PNotEqualsNPFixedOppositeSemanticQuotationExact where

------------------------------------------------------------------------
-- FIXED-PROGRAM-ONLY OPPOSITE SEMANTIC QUOTATION
--
-- OppositeSemanticProgramQuotationExact asks for semantic quotation correctness
-- for EVERY finite program.  Its decision-failure proof uses only one:
--
--   oppositeFixedPointProgram code.
--
-- This owner removes the unnecessary universal program obligation.  One Cook
-- formula is enough, provided it is SAT iff the canonical fixed program returns
-- true under the constant quotation sending every quoted program to that same
-- formula.
--
-- This is a strict weakening of the construction premise, not a strengthening
-- of the conclusion: it still produces a concrete SATDecisionFailure.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Unit using (tt)
open import Data.Empty using (⊥)
open import Data.Maybe.Base using (just)
open import Relation.Binary.PropositionalEquality using (sym; trans)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.PNotEqualsNPDirectSATLowerBoundExact as Direct
import DASHI.Mathematics.Complexity.PNotEqualsNPCandidateActualSelfInstantiationBoundaryExact as Actual
import DASHI.Mathematics.Complexity.PNotEqualsNPFiniteSelfSpecializingCodeExact as Code
import DASHI.Mathematics.Complexity.PNotEqualsNPOppositeSemanticProgramQuotationExact as Opposite

------------------------------------------------------------------------
-- Constant quotation: only the canonical fixed program's semantics matter.
------------------------------------------------------------------------

constantQuotation :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    {code : Actual.CandidateCodeRealization candidate} →
  Cook.BooleanFormula →
  Opposite.OppositeProgramQuotation code
constantQuotation formula = record
  { Opposite.quoteProgram = λ program → formula }

fixedProgram :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (code : Actual.CandidateCodeRealization candidate) →
  Code.Program (Opposite.OppositeQuotedPrimitive code)
fixedProgram =
  Opposite.oppositeFixedPointProgram

fixedRun :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (code : Actual.CandidateCodeRealization candidate)
    (formula : Cook.BooleanFormula) →
  Data.Maybe.Base.Maybe Bool
fixedRun code formula =
  Code.run1
    (Opposite.oppositePrimitiveSemantics
      code
      (constantQuotation formula))
    (fixedProgram code)
    tt

fixedRunExact :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (code : Actual.CandidateCodeRealization candidate)
    (formula : Cook.BooleanFormula) →
  fixedRun code formula
  ≡
  just
    (Opposite.notBool
      (Direct.decide candidate formula))
fixedRunExact code formula =
  Opposite.oppositeFixedPointRunsExact
    code
    (constantQuotation formula)

------------------------------------------------------------------------
-- Minimal semantic quotation for the one fixed program.
------------------------------------------------------------------------

record FixedSemanticQuotation
    {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (code : Actual.CandidateCodeRealization candidate) : Set₁ where
  field
    formula : Cook.BooleanFormula

    trueRunGivesSAT :
      fixedRun code formula ≡ just true →
      Cook.Satisfiable formula

    satGivesTrueRun :
      Cook.Satisfiable formula →
      fixedRun code formula ≡ just true

open FixedSemanticQuotation public

------------------------------------------------------------------------
-- Same diagonal contradiction, with no all-program quotation premise.
------------------------------------------------------------------------

fixedSemanticQuotationGivesDecisionFailure :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (code : Actual.CandidateCodeRealization candidate) →
  FixedSemanticQuotation code →
  Direct.SATDecisionFailure candidate
fixedSemanticQuotationGivesDecisionFailure
    {candidate = candidate}
    code
    semantic
    with Direct.decide candidate (formula semantic)
... | false =
  Direct.falseNegative
    (formula semantic)
    fixedSAT
    refl
  where
    fixedRunTrue :
      fixedRun code (formula semantic)
      ≡ just true
    fixedRunTrue =
      fixedRunExact code (formula semantic)

    fixedSAT :
      Cook.Satisfiable (formula semantic)
    fixedSAT =
      trueRunGivesSAT semantic fixedRunTrue

... | true =
  Direct.falsePositive
    (formula semantic)
    refl
    fixedUnsatisfiable
  where
    fixedRunFalse :
      fixedRun code (formula semantic)
      ≡ just false
    fixedRunFalse =
      fixedRunExact code (formula semantic)

    justInjective :
      ∀ {left right : Bool} →
      just left ≡ just right →
      left ≡ right
    justInjective refl = refl

    falseNotTrue : false ≡ true → ⊥
    falseNotTrue ()

    fixedUnsatisfiable :
      Cook.Satisfiable (formula semantic) → ⊥
    fixedUnsatisfiable satisfiable =
      falseNotTrue
        (justInjective
          (trans
            (sym fixedRunFalse)
            (satGivesTrueRun semantic satisfiable)))

record FixedSemanticQuotationProducer
    (cost : PR.PolynomialCostModel Cook.BooleanFormula) : Set₂ where
  field
    candidateCode :
      (candidate : Direct.PolynomialSATDeciderCandidate cost) →
      Actual.CandidateCodeRealization candidate

    semanticQuotation :
      (candidate : Direct.PolynomialSATDeciderCandidate cost) →
      FixedSemanticQuotation (candidateCode candidate)

open FixedSemanticQuotationProducer public

fixedSemanticProducerGivesUniversalFailure :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula} →
  FixedSemanticQuotationProducer cost →
  Direct.UniversalPolynomialSATDecisionFailure cost
fixedSemanticProducerGivesUniversalFailure producer candidate =
  fixedSemanticQuotationGivesDecisionFailure
    (candidateCode producer candidate)
    (semanticQuotation producer candidate)

------------------------------------------------------------------------
-- FRONTIER CONSEQUENCE
--
-- A general concrete interpreter for arbitrary Program syntax is unnecessary
-- for the diagonal theorem.  The remaining concrete object can be specialized
-- to the ONE canonical fixed program:
--
--   fixed finite opposite computation
--      -> one concrete tape machine/input/exact clock
--      -> Cook formula of that exact run
--      -> accepting iff fixed abstract run returns true.
--
-- This removes a universal-program dimension from the implementation wall.
------------------------------------------------------------------------
