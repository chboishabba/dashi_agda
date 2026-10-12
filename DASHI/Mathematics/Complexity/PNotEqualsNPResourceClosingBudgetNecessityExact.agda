module DASHI.Mathematics.Complexity.PNotEqualsNPResourceClosingBudgetNecessityExact where

------------------------------------------------------------------------
-- NECESSARY NUMERICAL CONDITIONS FOR RESOURCE-CLOSING SELF-QUOTATION
--
-- A ResourceClosingFixedProgramCompilation decomposes the exact Cook budget:
--
--   T = prefix + candidate(ownCookFormula) + suffix.
--
-- Therefore the candidate's exact execution on the self-generated Cook formula
-- must itself fit inside T.  This is a necessary condition on any proposed
-- diagonal constructor; it does not assert that such a constructor exists.
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
candidateOwnStepsFitCookBudget {clocked = clocked} resource =
  subst
    (λ total → candidateOwnSteps resource ≤ total)
    (Resource.totalStepsExact resource)
    beforeTransport
  where
    prefix = Resource.prefixSteps resource
    middle = candidateOwnSteps resource
    suffix = Resource.suffixSteps resource

    middleBelowPrefixMiddle : middle ≤ prefix + middle
    middleBelowPrefixMiddle =
      NatP.m≤n+m middle prefix

    prefixMiddleBelowTotal :
      prefix + middle ≤ (prefix + middle) + suffix
    prefixMiddleBelowTotal =
      NatP.m≤m+n (prefix + middle) suffix

    beforeTransport :
      middle ≤ (prefix + middle) + suffix
    beforeTransport =
      NatP.≤-trans
        middleBelowPrefixMiddle
        prefixMiddleBelowTotal

prefixFitsCookBudget :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    {clocked : Clocked.PolynomiallyClockedStandardCandidate candidate}
    (resource : Resource.ResourceClosingFixedProgramCompilation clocked) →
  Resource.prefixSteps resource
  ≤ Opposite.steps (Resource.fixed resource)
prefixFitsCookBudget {clocked = clocked} resource =
  subst
    (λ total → Resource.prefixSteps resource ≤ total)
    (Resource.totalStepsExact resource)
    (NatP.m≤m+n
      (Resource.prefixSteps resource)
      (candidateOwnSteps resource + Resource.suffixSteps resource))

------------------------------------------------------------------------
-- FRONTIER CONSEQUENCE
--
-- Any successful self-quotation construction must satisfy
--
--   candidateSteps(own Cook formula) <= T
--
-- while the own Cook formula itself grows with the exact tableau budget T.
-- This is the precise scale interface where the existing Cook-formula growth
-- theorems and the candidate's polynomial clock meet.  No reverse implication
-- is claimed: satisfying the inequality does not construct the prefix.
------------------------------------------------------------------------
