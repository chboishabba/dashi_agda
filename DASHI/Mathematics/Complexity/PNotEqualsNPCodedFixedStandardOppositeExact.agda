module DASHI.Mathematics.Complexity.PNotEqualsNPCodedFixedStandardOppositeExact where

------------------------------------------------------------------------
-- LOW-UNIVERSE CODE FOR THE FIXED OPPOSITE TARGET ITSELF
--
-- The virtual query serializer consumes CodedFiniteStandardTM.  The older
-- fixed-opposite carrier only promised a finite presentation.  This owner
-- removes that mismatch by making the diagonal target born in coded syntax and
-- forgetting it to the existing finite-presented carrier definitionally.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.PNotEqualsNPDirectSATLowerBoundExact as Direct
import DASHI.Mathematics.Complexity.PNotEqualsNPCandidateActualSelfInstantiationBoundaryExact as Actual
import DASHI.Mathematics.Complexity.PNotEqualsNPFixedStandardOppositeQuotationExact as Fixed
import DASHI.Mathematics.Complexity.CodedFiniteStandardMachineExact as Coded
import DASHI.Mathematics.Complexity.StandardFiniteTapePresentationExact as Presented
import DASHI.Mathematics.Complexity.ConcreteTapeRuleSelectorExact as Selector
import DASHI.Mathematics.Complexity.ConcreteTapeInputInitialRowExact as Input
import DASHI.Mathematics.Complexity.GuardedCookFormulaDescriptionExact as Description

record CodedFixedStandardOppositeMachine
    {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (candidateCode : Actual.CandidateCodeRealization candidate) : Set₂ where
  field
    targetCode : Coded.CodedFiniteStandardTM

    nonemptyRules :
      Selector.NonemptyRuleTable
        (Presented.finitePresentedStandardToConcrete
          (Coded.decodeCodedStandardTM targetCode))

    input :
      Input.InputWord
        (Presented.finitePresentedStandardToConcrete
          (Coded.decodeCodedStandardTM targetCode))

    steps : Nat

open CodedFixedStandardOppositeMachine public

forgetCodedFixed :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    {candidateCode : Actual.CandidateCodeRealization candidate} →
  CodedFixedStandardOppositeMachine candidateCode →
  Fixed.FixedStandardOppositeMachine candidateCode
forgetCodedFixed coded = record
  { Fixed.presentation = Coded.decodeCodedStandardTM (targetCode coded)
  ; Fixed.stateCoverage = Coded.codedStateCoverage (targetCode coded)
  ; Fixed.symbolCoverage = Coded.codedSymbolCoverage (targetCode coded)
  ; Fixed.nonemptyRules = nonemptyRules coded
  ; Fixed.input = input coded
  ; Fixed.steps = steps coded
  }

codedFixedDescription :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    {candidateCode : Actual.CandidateCodeRealization candidate} →
  CodedFixedStandardOppositeMachine candidateCode →
  Description.GuardedCookFormulaDescription
codedFixedDescription coded = record
  { Description.code = targetCode coded
  ; Description.nonemptyRules = nonemptyRules coded
  ; Description.input = input coded
  ; Description.steps = steps coded
  }

codedFixedCookFormulaExact :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    {candidateCode : Actual.CandidateCodeRealization candidate}
    (coded : CodedFixedStandardOppositeMachine candidateCode) →
  Description.formula (codedFixedDescription coded)
  ≡ Fixed.fixedCookFormula (forgetCodedFixed coded)
codedFixedCookFormulaExact coded = refl

codedFixedPresentationExact :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    {candidateCode : Actual.CandidateCodeRealization candidate}
    (coded : CodedFixedStandardOppositeMachine candidateCode) →
  Fixed.presentation (forgetCodedFixed coded)
  ≡ Coded.decodeCodedStandardTM (targetCode coded)
codedFixedPresentationExact coded = refl

------------------------------------------------------------------------
-- CONSEQUENCE
--
-- The active virtual diagonal can now use one SAME coded target object for:
--   * finite standard execution after decoding;
--   * exact guarded Cook construction;
--   * answer-blind indexed query serialization.
-- No reverse coding theorem for arbitrary finite presentations is assumed.
------------------------------------------------------------------------
