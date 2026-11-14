module DASHI.Mathematics.Complexity.PNotEqualsNPCodedFixedOwnCookSuccessfulWorkLowerExact where

------------------------------------------------------------------------
-- SAME-OBJECT WORK SANDWICH FOR THE FIXED OPPOSITE TARGET'S OWN COOK BITS
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Maybe using (just)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Nat.Base using (_≤_)
open import Relation.Binary.PropositionalEquality using (trans)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.PNotEqualsNPDirectSATLowerBoundExact as Direct
import DASHI.Mathematics.Complexity.PNotEqualsNPCandidateActualSelfInstantiationBoundaryExact as Actual
import DASHI.Mathematics.Complexity.CodedFiniteStandardMachineExact as Coded
import DASHI.Mathematics.Complexity.PNotEqualsNPCodedFixedStandardOppositeExact as CodedFixed
import DASHI.Mathematics.Complexity.PNotEqualsNPCodedFixedOwnCookStreamingCostExact as Own
import DASHI.Mathematics.Complexity.GuardedCookFormulaDescriptionExact as Description
import DASHI.Mathematics.Complexity.GuardedCookBitQueryCodeExact as Query
import DASHI.Mathematics.Complexity.GuardedCookBitQuerySemanticsExact as Semantics
import DASHI.Mathematics.Complexity.GuardedCookFixedDescriptionStreamingCostExact as Cost
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalCookLevinStreamingBitCostedExact as CostedBit
import DASHI.Mathematics.Complexity.ConcreteTapeStreamingBitSuccessfulWorkLowerExact as Lower

ownCookSuccessfulWorkLower :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    {candidateCode : Actual.CandidateCodeRealization candidate}
    (coded : CodedFixed.CodedFixedStandardOppositeMachine candidateCode)
    (index : Nat)
    (bit : Bool) →
  Semantics.queryAnswer
      (Description.atIndex (Own.ownDescription coded) index)
    ≡ just bit →
  suc index ≤ CostedBit.work (Own.ownCookBitCosted coded index)
ownCookSuccessfulWorkLower coded index bit semantic =
  Lower.streamedCookBitSuccessfulWorkLower
    (Coded.codedStateCoverage
      (Description.code (Own.ownDescription coded)))
    (Coded.codedSymbolCoverage
      (Description.code (Own.ownDescription coded)))
    (Description.nonemptyRules (Own.ownDescription coded))
    (Description.steps (Own.ownDescription coded))
    (Cost.descriptionCols (Own.ownDescription coded))
    (Cost.descriptionInitialTarget (Own.ownDescription coded))
    index bit exactResult
  where
    exactResult :
      CostedBit.result (Own.ownCookBitCosted coded index) ≡ just bit
    exactResult =
      trans
        (Own.ownCookBitCostedSemanticExact coded index)
        semantic

ownCookSuccessfulWorkUpper :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    {candidateCode : Actual.CandidateCodeRealization candidate}
    (coded : CodedFixed.CodedFixedStandardOppositeMachine candidateCode)
    (index : Nat) →
  CostedBit.work (Own.ownCookBitCosted coded index)
  ≤ Cost.fixedDescriptionLinearBudget
      (Own.ownDescription coded)
      (Query.queryBitLength
        (Description.atIndex (Own.ownDescription coded) index))
ownCookSuccessfulWorkUpper =
  Own.ownCookBitCostedWorkLinear

------------------------------------------------------------------------
-- CONSEQUENCE
--
-- For every in-range own-Cook bit, the currently proved evaluator is squeezed:
--
--   i + 1
--     <= actual costed streamed work
--     <= C_D * (canonical query length + 1).
--
-- This cleanly separates intrinsic indexed-access work from the still-open
-- standard-TM compiler coefficient.  A compiler receipt must preserve output
-- and pay its simulation overhead; it cannot erase the lower endpoint.
------------------------------------------------------------------------
