module DASHI.Mathematics.Complexity.PNotEqualsNPFixedWidthQuotedCorrectnessBoundaryExact where

------------------------------------------------------------------------
-- CORRECT SAT DECISION ON THE CURRENT SELF-QUOTATION
--
-- SemanticInertnessExact proves the fixed-width candidate quotation is always
-- satisfiable.  Therefore a genuinely correct SAT decider MUST return true on
-- that same-object root.
--
-- Consequences:
--   * returning false is already a concrete SATDecisionFailure;
--   * under SAT-in-P correctness, the operational fixed program returns true;
--   * no opposite-polarity diagonal can be obtained from the present structural
--     quotation without adding a new semantics-bearing execution encoding.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Unit using (tt)
open import Data.Maybe.Base using (just)
open import Relation.Binary.PropositionalEquality using (trans)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.PNotEqualsNPClayCoreExact as Clay
import DASHI.Mathematics.Complexity.PNotEqualsNPDirectSATLowerBoundExact as Direct
import DASHI.Mathematics.Complexity.PNotEqualsNPCandidateActualSelfInstantiationBoundaryExact as Actual
import DASHI.Mathematics.Complexity.PNotEqualsNPFiniteSelfSpecializingCodeExact as Code
import DASHI.Mathematics.Complexity.PNotEqualsNPCandidateCodeFormulaQuotationExact as CodeQuote
import DASHI.Mathematics.Complexity.PNotEqualsNPCandidateQuotedSelfApplicationExact as SelfQuote
import DASHI.Mathematics.Complexity.PNotEqualsNPFixedWidthCandidateQuotedRootExact as Fixed
import DASHI.Mathematics.Complexity.PNotEqualsNPFixedWidthQuotedRootSemanticInertnessExact as Inert
import DASHI.Mathematics.Complexity.PNotEqualsNPBoundedSelfReferenceWellFoundedExact as Q2

------------------------------------------------------------------------
-- Any arbitrary polynomial candidate that returns false on its fixed-width
-- quotation already exhibits a concrete false negative.
------------------------------------------------------------------------

fixedWidthQuotedFalseIsDecisionFailure :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (code : Actual.CandidateCodeRealization candidate)
    (codec :
      CodeQuote.FixedWidthCandidateCodeCodec
        (Actual.CandidateCodeRealization.CandidateCode code)) →
  Direct.decide candidate
      (Q2.currentFormula
        (Fixed.fixedWidthCandidateQuotedState code codec))
    ≡ false →
  Direct.SATDecisionFailure candidate
fixedWidthQuotedFalseIsDecisionFailure code codec returnedFalse =
  Direct.falseNegative
    (Q2.currentFormula
      (Fixed.fixedWidthCandidateQuotedState code codec))
    (Inert.fixedWidthCandidateQuotedRootIsSatisfiable code codec)
    returnedFalse

------------------------------------------------------------------------
-- Specialization to a candidate induced by a correct SAT-in-P witness.
------------------------------------------------------------------------

satPCandidate :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula} →
  PR.InP cost Clay.SATLanguage →
  Direct.PolynomialSATDeciderCandidate cost
satPCandidate =
  Direct.inPToPolynomialSATDeciderCandidate

correctSATCandidateAcceptsFixedWidthQuotation :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    (satP : PR.InP cost Clay.SATLanguage)
    (code : Actual.CandidateCodeRealization (satPCandidate satP))
    (codec :
      CodeQuote.FixedWidthCandidateCodeCodec
        (Actual.CandidateCodeRealization.CandidateCode code)) →
  Direct.decide
      (satPCandidate satP)
      (Q2.currentFormula
        (Fixed.fixedWidthCandidateQuotedState code codec))
  ≡ true
correctSATCandidateAcceptsFixedWidthQuotation satP code codec =
  PR.complete
    satP
    (Q2.currentFormula
      (Fixed.fixedWidthCandidateQuotedState code codec))
    (Inert.fixedWidthCandidateQuotedRootIsSatisfiable code codec)

------------------------------------------------------------------------
-- Hence the literal operational self-application returns true for a correct
-- SAT candidate on this quotation.
------------------------------------------------------------------------

correctSATFixedProgramReturnsTrue :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    (satP : PR.InP cost Clay.SATLanguage)
    (code : Actual.CandidateCodeRealization (satPCandidate satP))
    (codec :
      CodeQuote.FixedWidthCandidateCodeCodec
        (Actual.CandidateCodeRealization.CandidateCode code)) →
  Code.run1
      (SelfQuote.candidateQuotedPrimitiveSemantics
        code
        (SelfQuote.structuralProgramFormulaQuotation
          (Fixed.fixedWidthCandidateCodeQuotation code codec)))
      (SelfQuote.candidateQuotedFixedPointProgram code)
      tt
  ≡
  just true
correctSATFixedProgramReturnsTrue satP code codec =
  trans
    (Fixed.fixedWidthCandidateQuotedRunsCandidateOnCurrentFormula
      code codec)
    (congJust
      (correctSATCandidateAcceptsFixedWidthQuotation
        satP code codec))
  where
    congJust :
      ∀ {left right} →
      left ≡ right →
      just left ≡ just right
    congJust refl = refl

------------------------------------------------------------------------
-- FRONTIER CONSEQUENCE
--
-- The current self-quotation route does not diagonalize SAT.  Under the very
-- SAT-in-P hypothesis used for contradiction it computes TRUE on a formula
-- independently proved satisfiable.
--
-- The surviving Clay-critical object must therefore be a DIFFERENT quotation:
-- a semantics-bearing execution/Cook-Levin formula whose satisfiability is
-- linked to the candidate's own run in the required opposite polarity.
------------------------------------------------------------------------
