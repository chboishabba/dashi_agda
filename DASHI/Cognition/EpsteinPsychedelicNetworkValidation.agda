module DASHI.Cognition.EpsteinPsychedelicNetworkValidation where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Cognition.EpsteinPsychedelicSourceAtlasExact as Sources
import DASHI.Cognition.EpsteinPsychedelicNetworkEvidenceExact as Network
import DASHI.Cognition.EpsteinPsychedelicParetoSnowballExact as Pareto

canonicalEpsteinPsychedelicBoundary :
  Network.canonicalEpsteinPsychedelicNetworkBoundary ≡
  Network.epstein-psychedelic-network-boundary
    true true true true true true false false false false false
canonicalEpsteinPsychedelicBoundary = refl

sourceBoundaryKeepsAdministrationOpen :
  Sources.documentedInterestImpliesAdministration
    Sources.canonicalEpsteinPsychedelicSourceBoundary ≡ false
sourceBoundaryKeepsAdministrationOpen = refl

sourceBoundaryKeepsDirectMAPSFundingOpen :
  Sources.sourceMentionsMAPSImpliesEpsteinFundedMAPS
    Sources.canonicalEpsteinPsychedelicSourceBoundary ≡ false
sourceBoundaryKeepsDirectMAPSFundingOpen = refl

fundingSettlementStillOpen :
  Sources.transferStatementEqualsBankSettlement
    Sources.canonicalEpsteinPsychedelicSourceBoundary ≡ false
fundingSettlementStillOpen = refl

fundingInstructionStillOpen :
  Sources.fundingInstructionEqualsCompletedPayment
    Sources.canonicalEpsteinPsychedelicSourceBoundary ≡ false
fundingInstructionStillOpen = refl

brokerageAttributionDoesNotPayCompletedIntroduction :
  Network.completedThirdPartyIntroductionPaid Network.yuAttributesEpsteinBrokerage ≡ false
brokerageAttributionDoesNotPayCompletedIntroduction = refl

kuhnIntroductionObserved :
  Network.acknowledgedByIntroducedParty Network.kuhnIntroductionReceipt ≡ true
kuhnIntroductionObserved = refl

kuhnIntroductionPurposeBounded :
  Network.psychedelicPurposeEstablished Network.kuhnIntroductionReceipt ≡ false
kuhnIntroductionPurposeBounded = refl

conveningProposalNotCompletion :
  Network.completedAsProposed Network.jointCommunityConveningProposal ≡ false
conveningProposalNotCompletion = refl

currentEpsteinPsychedelicRoute :
  Pareto.currentFrontierExact ≡ Pareto.currentFrontierExact
currentEpsteinPsychedelicRoute = refl
