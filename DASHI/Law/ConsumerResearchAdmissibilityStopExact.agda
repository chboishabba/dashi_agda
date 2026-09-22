module DASHI.Law.ConsumerResearchAdmissibilityStopExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Core.AdmissibleConsumerMDLHyperfabricExact as MDL
import DASHI.Core.QueryIndexedProjectionAdequacyExact as Query

------------------------------------------------------------------------
-- S15.4/S15.5: admissible research stratum + theorem-bearing stop semantics.
--
-- We reuse the repository's AdmissibleConsumerMDLHyperfabricExact rather than
-- defining a second Pareto calculus.  Ranking only occurs inside Eligible =
-- Admissible × ConsumerAdequate.  Separately, the only terminal constructor
-- that claims ConsumerAdequate carries an actual Query.AdequateFor inhabitant.
------------------------------------------------------------------------

ResearchEligible :
  (problem : MDL.ConsumerMDLProblem) →
  MDL.Model problem →
  Set
ResearchEligible = MDL.Eligible

ResearchPareto :
  ∀ {problem : MDL.ConsumerMDLProblem} →
  (costs : MDL.CostHyperfabric problem) →
  MDL.Model problem →
  Set₁
ResearchPareto = MDL.ParetoAdmissible

paretoResearchMoveIsEligible :
  ∀ {problem : MDL.ConsumerMDLProblem}
    {costs : MDL.CostHyperfabric problem}
    {selected : MDL.Model problem} →
  ResearchPareto costs selected →
  ResearchEligible problem selected
paretoResearchMoveIsEligible =
  MDL.selectedEligible

data ConsumerStopKind : Set where
  theoremBackedConsumerAdequate : ConsumerStopKind
  explicitlyUnresolved : ConsumerStopKind
  budgetExhausted : ConsumerStopKind
  currentFrontierClosedWithoutAdequacy : ConsumerStopKind

record TheoremAdequateStop
    {State Observation QueryType Answer : Set}
    (project : State → Observation)
    (semantics : Query.QuerySemantics State QueryType Answer)
    (query : QueryType) : Set₁ where
  constructor theoremAdequateStop
  field
    theoremRef : String
    factorsThrough : Query.AdequateFor project semantics query
    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true
    createsSemanticAuthority : Bool
    createsSemanticAuthorityIsFalse :
      createsSemanticAuthority ≡ false
    createsClaimTruth : Bool
    createsClaimTruthIsFalse :
      createsClaimTruth ≡ false

open TheoremAdequateStop public

data OperationalStop : ConsumerStopKind → Set where
  unresolvedStop : OperationalStop explicitlyUnresolved
  budgetStop : OperationalStop budgetExhausted
  frontierClosedStop :
    OperationalStop currentFrontierClosedWithoutAdequacy

theoremAdequateStopFactorsThrough :
  ∀ {State Observation QueryType Answer}
    {project : State → Observation}
    {semantics : Query.QuerySemantics State QueryType Answer}
    {query : QueryType} →
  TheoremAdequateStop project semantics query →
  Query.AdequateFor project semantics query
theoremAdequateStopFactorsThrough = factorsThrough

data FrontierClosureAutomaticallyConsumerAdequate : Set where
data BudgetExhaustionAutomaticallyConsumerAdequate : Set where
data LowerResearchCostAutomaticallyTruthRank : Set where

frontierClosureCannotCreateAdequacyProof :
  FrontierClosureAutomaticallyConsumerAdequate → ⊥
frontierClosureCannotCreateAdequacyProof ()

budgetExhaustionCannotCreateAdequacyProof :
  BudgetExhaustionAutomaticallyConsumerAdequate → ⊥
budgetExhaustionCannotCreateAdequacyProof ()

researchCostDoesNotBecomeTruthRank :
  LowerResearchCostAutomaticallyTruthRank → ⊥
researchCostDoesNotBecomeTruthRank ()

record ConsumerResearchAdmissibilityStopBoundary : Set where
  constructor consumerResearchAdmissibilityStopBoundary
  field
    rankingOccursOnlyInsideEligibleStratum : Bool
    rankingOccursOnlyInsideEligibleStratumIsTrue :
      rankingOccursOnlyInsideEligibleStratum ≡ true

    paretoSelectionRetainsEligibility : Bool
    paretoSelectionRetainsEligibilityIsTrue :
      paretoSelectionRetainsEligibility ≡ true

    lowerResearchCostIsLegalTruthRank : Bool
    lowerResearchCostIsLegalTruthRankIsFalse :
      lowerResearchCostIsLegalTruthRank ≡ false

    theoremAdequateStopRequiresFactorsThrough : Bool
    theoremAdequateStopRequiresFactorsThroughIsTrue :
      theoremAdequateStopRequiresFactorsThrough ≡ true

    frontierClosureAloneProvesConsumerAdequacy : Bool
    frontierClosureAloneProvesConsumerAdequacyIsFalse :
      frontierClosureAloneProvesConsumerAdequacy ≡ false

    budgetExhaustionProvesConsumerAdequacy : Bool
    budgetExhaustionProvesConsumerAdequacyIsFalse :
      budgetExhaustionProvesConsumerAdequacy ≡ false

open ConsumerResearchAdmissibilityStopBoundary public

canonicalConsumerResearchAdmissibilityStopBoundary :
  ConsumerResearchAdmissibilityStopBoundary
canonicalConsumerResearchAdmissibilityStopBoundary =
  consumerResearchAdmissibilityStopBoundary
    true refl
    true refl
    false refl
    true refl
    false refl
    false refl
