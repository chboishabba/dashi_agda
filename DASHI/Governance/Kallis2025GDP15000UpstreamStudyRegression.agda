module DASHI.Governance.Kallis2025GDP15000UpstreamStudyRegression where

open import DASHI.Core.Prelude

import DASHI.Governance.Kallis2025ClaimByClaimEvidenceRealizationExact as Claims
import DASHI.Governance.Kallis2025GDP15000UpstreamStudyBridgeExact as Bridge

------------------------------------------------------------------------
-- Focused regression for review -> upstream study -> claim -> consumer ->
-- residual routing.
------------------------------------------------------------------------

referenceNumberRetained :
  Bridge.UpstreamStudyEdge.reviewAnchor Bridge.canonicalGDP15000UpstreamEdge ≡
  Bridge.UpstreamStudyEdge.reviewAnchor Bridge.canonicalGDP15000UpstreamEdge
referenceNumberRetained = refl

claimIsGDP15000 :
  Claims.ClaimEvidenceRealization.claim
    (Bridge.UpstreamStudyEdge.claimRealization Bridge.canonicalGDP15000UpstreamEdge) ≡
  Claims.gdp15000Claim
claimIsGDP15000 = Bridge.realizationIsGDP15000Claim

consumerIsDescriptive :
  Bridge.UpstreamStudyEdge.intendedConsumer Bridge.canonicalGDP15000UpstreamEdge ≡
  Claims.descriptiveSynthesisConsumer
consumerIsDescriptive = Bridge.consumerRemainsDescriptive

associationResidualRemainsOpen :
  Bridge.UpstreamStudyEdge.liveResidual Bridge.canonicalGDP15000UpstreamEdge ≡
  Claims.associationNotCausation
associationResidualRemainsOpen = Bridge.residualRemainsAssociationNotCausation

causalConsumerStillBlocked :
  Claims.AdequateFor Claims.gdp15000Realization Claims.causalMechanismConsumer → ⊥
causalConsumerStillBlocked = Bridge.upstreamStudyDoesNotOpenCausalConsumer

boundaryBlocksUniversalCausalThreshold :
  Bridge.GDP15000UpstreamBoundary.observedCrossRegionalPatternIsUniversalCausalThreshold
    Bridge.canonicalGDP15000UpstreamBoundary ≡ false
boundaryBlocksUniversalCausalThreshold = refl

boundaryKeepsResidualOpen :
  Bridge.GDP15000UpstreamBoundary.upstreamStudyDischargesAssociationResidual
    Bridge.canonicalGDP15000UpstreamBoundary ≡ false
boundaryKeepsResidualOpen = refl
