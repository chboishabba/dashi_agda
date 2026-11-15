module DASHI.Mathematics.Complexity.PNotEqualsNPCodedFixedOwnCookStreamingCostExact where

------------------------------------------------------------------------
-- SAME-OBJECT COSTED STREAMING FOR THE CODED OPPOSITE TARGET'S OWN COOK FORMULA
--
-- No generic formula or machine is introduced here.  The description is
-- definitionally `codedFixedDescription coded`, whose formula is already proved
-- equal to the fixed opposite target's actual guarded Cook formula.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Maybe using (Maybe)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat.Base using (_≤_)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.PNotEqualsNPDirectSATLowerBoundExact as Direct
import DASHI.Mathematics.Complexity.PNotEqualsNPCandidateActualSelfInstantiationBoundaryExact as Actual
import DASHI.Mathematics.Complexity.PNotEqualsNPFixedStandardOppositeQuotationExact as Fixed
import DASHI.Mathematics.Complexity.PNotEqualsNPCodedFixedStandardOppositeExact as CodedFixed
import DASHI.Mathematics.Complexity.GuardedCookFormulaDescriptionExact as Description
import DASHI.Mathematics.Complexity.GuardedCookBitQueryCodeExact as Query
import DASHI.Mathematics.Complexity.GuardedCookBitQuerySemanticsExact as Semantics
import DASHI.Mathematics.Complexity.GuardedCookFixedDescriptionStreamingCostExact as Cost
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalCookLevinStreamingBitCostedExact as CostedBit

ownDescription :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    {candidateCode : Actual.CandidateCodeRealization candidate} →
  CodedFixed.CodedFixedStandardOppositeMachine candidateCode →
  Description.GuardedCookFormulaDescription
ownDescription = CodedFixed.codedFixedDescription

ownCookBitCosted :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    {candidateCode : Actual.CandidateCodeRealization candidate}
    (coded : CodedFixed.CodedFixedStandardOppositeMachine candidateCode) →
  Nat →
  CostedBit.Costed (Maybe Bool)
ownCookBitCosted coded index =
  Cost.streamedQueryBitCosted (ownDescription coded) index

ownCookBitCostedSemanticExact :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    {candidateCode : Actual.CandidateCodeRealization candidate}
    (coded : CodedFixed.CodedFixedStandardOppositeMachine candidateCode)
    (index : Nat) →
  CostedBit.result (ownCookBitCosted coded index)
  ≡ Semantics.queryAnswer
      (Description.atIndex (ownDescription coded) index)
ownCookBitCostedSemanticExact coded index =
  Cost.streamedQueryBitCostedSemanticExact
    (ownDescription coded)
    index

ownCookBitCostedWorkLinear :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    {candidateCode : Actual.CandidateCodeRealization candidate}
    (coded : CodedFixed.CodedFixedStandardOppositeMachine candidateCode)
    (index : Nat) →
  CostedBit.work (ownCookBitCosted coded index)
  ≤ Cost.fixedDescriptionLinearBudget
      (ownDescription coded)
      (Query.queryBitLength
        (Description.atIndex (ownDescription coded) index))
ownCookBitCostedWorkLinear coded index =
  Cost.fixedDescriptionBitWorkLinearInCanonicalInput
    (ownDescription coded)
    index

ownCookFormulaSameObject :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    {candidateCode : Actual.CandidateCodeRealization candidate}
    (coded : CodedFixed.CodedFixedStandardOppositeMachine candidateCode) →
  Description.formula (ownDescription coded)
  ≡ Fixed.fixedCookFormula (CodedFixed.forgetCodedFixed coded)
ownCookFormulaSameObject =
  CodedFixed.codedFixedCookFormulaExact

------------------------------------------------------------------------
-- CONSEQUENCE
--
-- The remaining generator theorem is no longer about a generic semantic source:
-- we have an executable list-free evaluator and exact work bound for indexed
-- access to the SAME target's own Cook formula.  What remains is to compile this
-- finite recursion/work model into the coded target's literal standard-TM
-- execution, preserving output and charging a constant/polynomial step overhead.
------------------------------------------------------------------------
