module DASHI.Governance.SafeJustSituatedClaimAuthorityRegression where

open import DASHI.Core.Prelude
import DASHI.Core.SituatedClaimAuthoritySystemExact as Situated
import DASHI.Governance.SafeJustSituatedClaimAuthorityBridgeExact as Bridge

------------------------------------------------------------------------
-- Focused regression for the material/empirical + epistemic-authority weld.
------------------------------------------------------------------------

fanningQualified :
  Situated.QualifiedUse
    Bridge.safeJustSituatedClaimAuthoritySystem
    Bridge.safeJustResearchAgenda
    Bridge.safeJustIndicatorCategory
    Bridge.fanningBAUProjectionClaim
    Bridge.repositorySourceRegistryContext
    Bridge.forecastResearchConsumer
    Bridge.researchSynthesisUse
    Bridge.attributionAndResidualCarriage
fanningQualified = Bridge.fanningQualifiedResearchUse

kallisGDPQualified :
  Situated.QualifiedUse
    Bridge.safeJustSituatedClaimAuthoritySystem
    Bridge.safeJustResearchAgenda
    Bridge.safeJustIndicatorCategory
    Bridge.kallisGDP15000Claim
    Bridge.repositorySourceRegistryContext
    Bridge.descriptiveResearchConsumer
    Bridge.researchSynthesisUse
    Bridge.attributionAndResidualCarriage
kallisGDPQualified = Bridge.kallisGDPQualifiedResearchUse

fanningCausalPromotionBlocked :
  Situated.QualifiedUse
    Bridge.safeJustSituatedClaimAuthoritySystem
    Bridge.safeJustResearchAgenda
    Bridge.safeJustIndicatorCategory
    Bridge.fanningBAUProjectionClaim
    Bridge.repositorySourceRegistryContext
    Bridge.causalMechanismConsumer
    Bridge.causalPromotionUse
    Bridge.attributionAndResidualCarriage → ⊥
fanningCausalPromotionBlocked = Bridge.fanningCausalQualifiedUseImpossible

kallisPolicyPromotionBlocked :
  Situated.QualifiedUse
    Bridge.safeJustSituatedClaimAuthoritySystem
    Bridge.safeJustResearchAgenda
    Bridge.safeJustIndicatorCategory
    Bridge.kallisGDP15000Claim
    Bridge.repositorySourceRegistryContext
    Bridge.policyInterventionConsumer
    Bridge.policyInterventionUse
    Bridge.attributionAndResidualCarriage → ⊥
kallisPolicyPromotionBlocked = Bridge.kallisPolicyQualifiedUseImpossible

fanningDecisionAuthorityBlocked :
  Bridge.DecisionAuthorized
    Bridge.repositorySourceRegistryContext
    Bridge.fanningBAUProjectionClaim
    Bridge.policyInterventionUse → ⊥
fanningDecisionAuthorityBlocked = Bridge.fanningResearchUseDoesNotCreateDecisionAuthority

kallisDecisionAuthorityBlocked :
  Bridge.DecisionAuthorized
    Bridge.repositorySourceRegistryContext
    Bridge.kallisGDP15000Claim
    Bridge.policyInterventionUse → ⊥
kallisDecisionAuthorityBlocked = Bridge.kallisResearchUseDoesNotCreateDecisionAuthority

boundary : Bridge.SafeJustSituatedClaimAuthorityBoundary
boundary = Bridge.canonicalSafeJustSituatedClaimAuthorityBoundary
