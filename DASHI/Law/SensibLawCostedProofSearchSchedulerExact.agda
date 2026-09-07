module DASHI.Law.SensibLawCostedProofSearchSchedulerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Law.SensibLawSearchExecutionCostParetoExact as Cost
import DASHI.Law.SensibLawIterativeProofSearchStateMachineExact as Iterative
import DASHI.Law.SensibLawProofSearchParetoSaturationExact as Pareto

------------------------------------------------------------------------
-- COSTED PROOF-SEARCH SCHEDULER
--
-- The scheduler chooses among admissible legal research moves only after a
-- consumer declares the minimum useful proof-frontier reduction. Execution
-- strategy costs remain multi-axis; a scalar projection is optional and must be
-- declared separately.
------------------------------------------------------------------------

record MeetsProofReductionThreshold
    (move : Cost.LegalSearchMove)
    (threshold : Nat) : Set where
  constructor meetsProofReductionThreshold
  field
    enoughReduction : threshold ≤ Cost.expectedProofReduction move

open MeetsProofReductionThreshold public

record CostedLegalSearchChoice
    (threshold : Nat)
    (Declared : Cost.LegalSearchMove → Set) : Set₂ where
  constructor costedLegalSearchChoice
  field
    selected : Cost.LegalSearchMove
    selectedDeclared : Declared selected
    selectedMeetsThreshold : MeetsProofReductionThreshold selected threshold
    selectedUndominated :
      (alternative : Cost.LegalSearchMove) →
      Declared alternative →
      MeetsProofReductionThreshold alternative threshold →
      Cost.LegalSearchMoveDominates alternative selected →
      Cost.LegalSearchMoveDominates selected alternative
    consumerReference : String
    schedulerReference : String

open CostedLegalSearchChoice public

------------------------------------------------------------------------
-- Search iteration weld.
------------------------------------------------------------------------

record CostedSearchIteration : Set₁ where
  constructor costedSearchIteration
  field
    priorState : Iterative.ProofSearchState
    selectedMove : Cost.LegalSearchMove
    threshold : Nat
    thresholdReceipt : MeetsProofReductionThreshold selectedMove threshold
    transition : Iterative.ProofSearchTransition
    transitionStartsAtPriorReceipt : Set
    transitionCausedBySelectedMoveReceipt : Set
    posteriorState : Iterative.ProofSearchState
    posteriorMatchesTransitionReceipt : Set
    iterationReference : String

open CostedSearchIteration public

------------------------------------------------------------------------
-- Escalation policy: local/persisted work is preferred operationally when it
-- remains Pareto-competitive, but no theorem says offline is always superior.
------------------------------------------------------------------------

data ExecutionEscalationStage : Set where
  inspectLocalFixture
  inspectPersistedAuthorityReceipt
  inspectLocalWorldGraph
  governedLiveReferenceSearch
  governedExactAuthorityFetch
  governedBoundedCitationFollow
  : ExecutionEscalationStage

record EscalationDecision : Set₁ where
  constructor escalationDecision
  field
    consumerReference : String
    currentStage : ExecutionEscalationStage
    currentFrontierReference : String
    localCandidateReference : String
    persistedCandidateReference : String
    liveCandidateReference : String
    localOrPersistedDominatedReceipt : Set
    liveExpectedAdditionalReductionReceipt : Set
    liveGovernanceAdmissibilityReceipt : Set
    selectedNextStage : ExecutionEscalationStage
    decisionReference : String

open EscalationDecision public

------------------------------------------------------------------------
-- Saturation and cost remain distinct.
------------------------------------------------------------------------

record CostedStoppingDecision : Set₁ where
  constructor costedStoppingDecision
  field
    consumerReference : String
    continuation : Pareto.SearchContinuationDecision
    costSurfaceReference : String
    frontierReference : String
    continuationReceipt : Set
    stoppingReference : String

open CostedStoppingDecision public

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data ZeroNetworkCostForcesSelection : Set where
data GainThresholdMeansProofClosed : Set where
data CheapestAdmissibleMoveMustBeSelected : Set where
data LiveEscalationAllowedWithoutGovernance : Set where
data ExhaustedBudgetMeansPropositionFalse : Set where
data HighAuthorityFitnessMeansHighProofReduction : Set where

zeroNetworkDoesNotForceSelection : ZeroNetworkCostForcesSelection → ⊥
zeroNetworkDoesNotForceSelection ()

gainThresholdDoesNotMeanClosed : GainThresholdMeansProofClosed → ⊥
gainThresholdDoesNotMeanClosed ()

cheapestDoesNotAutomaticallyWin : CheapestAdmissibleMoveMustBeSelected → ⊥
cheapestDoesNotAutomaticallyWin ()

liveEscalationRequiresGovernance : LiveEscalationAllowedWithoutGovernance → ⊥
liveEscalationRequiresGovernance ()

budgetExhaustionDoesNotMeanFalse : ExhaustedBudgetMeansPropositionFalse → ⊥
budgetExhaustionDoesNotMeanFalse ()

authorityFitnessDoesNotEqualReduction : HighAuthorityFitnessMeansHighProofReduction → ⊥
authorityFitnessDoesNotEqualReduction ()

record CostedProofSearchSchedulerBoundary : Set where
  constructor costedProofSearchSchedulerBoundary
  field
    proofReductionThresholdPrecedesCostOptimisation : Bool
    proofReductionThresholdPrecedesCostOptimisationIsTrue :
      proofReductionThresholdPrecedesCostOptimisation ≡ true
    executionCostRemainsParetoVector : Bool
    executionCostRemainsParetoVectorIsTrue : executionCostRemainsParetoVector ≡ true
    offlineMayBePreferredWithoutBeingUniversallyBest : Bool
    offlineMayBePreferredWithoutBeingUniversallyBestIsTrue :
      offlineMayBePreferredWithoutBeingUniversallyBest ≡ true
    liveEscalationRequiresGovernance : Bool
    liveEscalationRequiresGovernanceIsTrue : liveEscalationRequiresGovernance ≡ true
    budgetExhaustionEqualsLegalRefutation : Bool
    budgetExhaustionEqualsLegalRefutationIsFalse :
      budgetExhaustionEqualsLegalRefutation ≡ false

canonicalCostedProofSearchSchedulerBoundary : CostedProofSearchSchedulerBoundary
canonicalCostedProofSearchSchedulerBoundary =
  costedProofSearchSchedulerBoundary true refl true refl true refl true refl false refl
