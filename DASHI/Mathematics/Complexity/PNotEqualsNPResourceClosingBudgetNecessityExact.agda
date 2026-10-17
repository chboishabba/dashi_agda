module DASHI.Mathematics.Complexity.PNotEqualsNPResourceClosingBudgetNecessityExact where

------------------------------------------------------------------------
-- NECESSARY NUMERICAL CONDITIONS FOR RESOURCE-CLOSING SELF-QUOTATION
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; _+_)
open import Data.Nat.Base using (_≤_)
import Data.Nat.Properties as NatP
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.PNotEqualsNPDirectSATLowerBoundExact as Direct
import DASHI.Mathematics.Complexity.PNotEqualsNPPolynomiallyClockedStandardCandidateExact as Clocked
import DASHI.Mathematics.Complexity.PNotEqualsNPStandardFiniteCandidateCodeExact as Candidate
import DASHI.Mathematics.Complexity.PNotEqualsNPFixedStandardOppositeQuotationExact as Opposite
import DASHI.Mathematics.Complexity.PNotEqualsNPResourceClosingStandardCompilerExact as Resource

candidateOwnSteps :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    {clocked : Clocked.PolynomiallyClockedStandardCandidate candidate} →
  Resource.ResourceClosingFixedProgramCompilation clocked → Nat
candidateOwnSteps {clocked = clocked} resource =
  Candidate.exactSteps
    (Clocked.standard clocked)
    (Opposite.fixedCookFormula (Resource.fixed resource))

candidateOwnStepsFitCookBudget :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    {clocked : Clocked.PolynomiallyClockedStandardCandidate candidate}
    (resource : Resource.ResourceClosingFixedProgramCompilation clocked) →
  candidateOwnSteps resource
  ≤ Opposite.steps (Resource.fixed resource)
candidateOwnStepsFitCookBudget resource =
  subst
    (λ total → candidateOwnSteps resource ≤ total)
    (Resource.totalStepsExact resource)
    beforeTransport
  where
    prefix = Resource.prefixSteps resource
    middle = candidateOwnSteps resource
    suffix = Resource.suffixSteps resource

    beforeTransport : middle ≤ (prefix + middle) + suffix
    beforeTransport =
      NatP.≤-trans
        (NatP.m≤n+m middle prefix)
        (NatP.m≤m+n (prefix + middle) suffix)

prefixFitsCookBudget :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    {clocked : Clocked.PolynomiallyClockedStandardCandidate candidate}
    (resource : Resource.ResourceClosingFixedProgramCompilation clocked) →
  Resource.prefixSteps resource
  ≤ Opposite.steps (Resource.fixed resource)
prefixFitsCookBudget resource =
  subst
    (λ total → Resource.prefixSteps resource ≤ total)
    (Resource.totalStepsExact resource)
    beforeTransport
  where
    prefix = Resource.prefixSteps resource
    middle = candidateOwnSteps resource
    suffix = Resource.suffixSteps resource

    beforeTransport : prefix ≤ (prefix + middle) + suffix
    beforeTransport =
      NatP.≤-trans
        (NatP.m≤m+n prefix middle)
        (NatP.m≤m+n (prefix + middle) suffix)

suffixFitsCookBudget :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    {clocked : Clocked.PolynomiallyClockedStandardCandidate candidate}
    (resource : Resource.ResourceClosingFixedProgramCompilation clocked) →
  Resource.suffixSteps resource
  ≤ Opposite.steps (Resource.fixed resource)
suffixFitsCookBudget resource =
  subst
    (λ total → Resource.suffixSteps resource ≤ total)
    (Resource.totalStepsExact resource)
    (NatP.m≤n+m
      (Resource.suffixSteps resource)
      (Resource.prefixSteps resource + candidateOwnSteps resource))

------------------------------------------------------------------------
-- FRONTIER CONSEQUENCE
--
-- Every phase must fit the same exact Cook budget.  In particular:
--
--   candidateSteps(own Cook formula) <= T.
--
-- The own Cook formula itself grows with T, so this theorem is the precise
-- numeric interface between Cook-quotation growth and the candidate clock.
-- It is only a necessary condition and never manufactures the prefix.
------------------------------------------------------------------------
