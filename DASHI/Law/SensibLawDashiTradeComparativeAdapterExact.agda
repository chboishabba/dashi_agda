module DASHI.Law.SensibLawDashiTradeComparativeAdapterExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Law.SensibLawChangeLocusExact as Locus
import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Finance.DashiTradeFibreBridgeExact as Fibre
import DASHI.Trading.DashiTradeDreamOptionConeExact as Dream

------------------------------------------------------------------------
-- M11 DASHITRADE COMPARATIVE ADAPTER
--
-- Quotient representation, policy, belief, actionability and realised outcome
-- remain independent coordinates. The adapter reuses the existing
-- non-factorability/actionability owners rather than deriving semantic status
-- from trading labels.
------------------------------------------------------------------------

data DashiTradeDifferenceKind : Set where
  rawMarketDifference : DashiTradeDifferenceKind
  observationDifference : DashiTradeDifferenceKind
  quotientRepresentationDifference : DashiTradeDifferenceKind
  thesisBeliefDifference : DashiTradeDifferenceKind
  policyRepresentationDifference : DashiTradeDifferenceKind
  admissibilityDifference : DashiTradeDifferenceKind
  actionOutcomeDifference : DashiTradeDifferenceKind

dashiTradeDifferenceLayer :
  DashiTradeDifferenceKind → Locus.ChangeLayer
dashiTradeDifferenceLayer rawMarketDifference = Locus.worldLayer
dashiTradeDifferenceLayer observationDifference = Locus.observationLayer
dashiTradeDifferenceLayer quotientRepresentationDifference =
  Locus.representationLayer
dashiTradeDifferenceLayer thesisBeliefDifference = Locus.beliefLayer
dashiTradeDifferenceLayer policyRepresentationDifference =
  Locus.representationLayer
dashiTradeDifferenceLayer admissibilityDifference =
  Locus.applicabilityLayer
dashiTradeDifferenceLayer actionOutcomeDifference =
  Locus.proofOutcomeLayer

beliefDifferenceIsBelief :
  dashiTradeDifferenceLayer thesisBeliefDifference ≡ Locus.beliefLayer
beliefDifferenceIsBelief = refl

shadowPolicyDifferenceIsRepresentation :
  dashiTradeDifferenceLayer policyRepresentationDifference
  ≡ Locus.representationLayer
shadowPolicyDifferenceIsRepresentation = refl

actionDifferenceIsOutcome :
  dashiTradeDifferenceLayer actionOutcomeDifference
  ≡ Locus.proofOutcomeLayer
actionDifferenceIsOutcome = refl

------------------------------------------------------------------------
-- Existing dashiTRADE theorem: same proposal is not enough to recover
-- relational actionability; arbitrary recharting cannot restore the erased
-- coordinate.
------------------------------------------------------------------------

sameProposalWitness :
  Dream.candidateObserver Dream.cleanLongState
  ≡ Dream.candidateObserver Dream.crowdedLongState
sameProposalWitness = Dream.sameLongProposal

buyStillDoesNotFactorThroughDirection :
  NF.FactorsThrough
    Dream.candidateObserver
    (λ state → Dream.actionAvailable state Dream.buyAction) →
  ⊥
buyStillDoesNotFactorThroughDirection =
  Dream.noDirectionOnlyBuyClassifier

rechartStillCannotRecoverBuyViability :
  ∀ {Chart : Set} →
  (rechart : Dream.Direction → Chart) →
  NF.FactorsThrough
    (λ state → rechart (Dream.candidateObserver state))
    (λ state → Dream.actionAvailable state Dream.buyAction) →
  ⊥
rechartStillCannotRecoverBuyViability =
  Dream.postprocessedDirectionStillCannotRecoverBuyViability

sameEndpointStillDoesNotEraseTrajectoryCost :
  Dream.totalCost (Dream.costFor Dream.lowTurnoverRoute)
  ≡ Dream.totalCost (Dream.costFor Dream.churnRoute) →
  ⊥
sameEndpointStillDoesNotEraseTrajectoryCost =
  Dream.sameEndpointDifferentTrajectoryCost

data QuotientEqualityImpliesRawWorldIdentity : Set where
data BeliefDeltaImpliesWorldDelta : Set where
data ActionDeltaImpliesWorldDelta : Set where
data JustificationChainProvesMarketCausation : Set where
data ProfitableTrajectoryProvesGlobalTheory : Set where

quotientEqualityDoesNotIdentifyRawWorld :
  QuotientEqualityImpliesRawWorldIdentity → ⊥
quotientEqualityDoesNotIdentifyRawWorld ()

beliefDeltaDoesNotBecomeWorldDelta :
  BeliefDeltaImpliesWorldDelta → ⊥
beliefDeltaDoesNotBecomeWorldDelta ()

actionDeltaDoesNotBecomeWorldDelta :
  ActionDeltaImpliesWorldDelta → ⊥
actionDeltaDoesNotBecomeWorldDelta ()

justificationChainDoesNotProveMarketCausation :
  JustificationChainProvesMarketCausation → ⊥
justificationChainDoesNotProveMarketCausation ()

profitableTrajectoryDoesNotProveGlobalTheory :
  ProfitableTrajectoryProvesGlobalTheory → ⊥
profitableTrajectoryDoesNotProveGlobalTheory ()

record DashiTradeComparativeBoundary : Set where
  constructor dashiTradeComparativeBoundary
  field
    quotientIsRepresentationNotWorldIdentity : Bool
    quotientIsRepresentationNotWorldIdentityIsTrue :
      quotientIsRepresentationNotWorldIdentity ≡ true

    richerQueryMayFailToFactorThroughQuotient : Bool
    richerQueryMayFailToFactorThroughQuotientIsTrue :
      richerQueryMayFailToFactorThroughQuotient ≡ true

    beliefIsSeparateChangeLayer : Bool
    beliefIsSeparateChangeLayerIsTrue :
      beliefIsSeparateChangeLayer ≡ true

    sameWorldDifferentPolicyRepresentationPossible : Bool
    sameWorldDifferentPolicyRepresentationPossibleIsTrue :
      sameWorldDifferentPolicyRepresentationPossible ≡ true

    actionOutcomeIsNotWorldInput : Bool
    actionOutcomeIsNotWorldInputIsTrue :
      actionOutcomeIsNotWorldInput ≡ true

    justificationChainCreatesCausalProof : Bool
    justificationChainCreatesCausalProofIsFalse :
      justificationChainCreatesCausalProof ≡ false

    realisedProfitCreatesGlobalTheoryTruth : Bool
    realisedProfitCreatesGlobalTheoryTruthIsFalse :
      realisedProfitCreatesGlobalTheoryTruth ≡ false

open DashiTradeComparativeBoundary public

canonicalDashiTradeComparativeBoundary : DashiTradeComparativeBoundary
canonicalDashiTradeComparativeBoundary =
  dashiTradeComparativeBoundary
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
