module DASHI.Governance.Kallis2025ClaimEvidenceRegression where

open import DASHI.Core.Prelude
import DASHI.Governance.Kallis2025ClaimAuthorityRoutingExact as Routing
import DASHI.Governance.Kallis2025EvidenceAtlasExact as Atlas
import DASHI.Governance.Kallis2025ClaimByClaimEvidenceRealizationExact as Claims

------------------------------------------------------------------------
-- Focused receipts for claim-by-claim Kallis evidence routing.
------------------------------------------------------------------------

gdpClaimUsesRef98 : Atlas.EvidenceAnchor.reviewReference Atlas.gdp15000Owner ≡ 98
gdpClaimUsesRef98 = refl

decouplingScenarioUsesRef49 :
  Atlas.EvidenceAnchor.reviewReference Atlas.optimisticTechnologyProjection ≡ 49
decouplingScenarioUsesRef49 = refl

provisioningClaimUsesRef185 :
  Atlas.EvidenceAnchor.reviewReference Atlas.provisioningSystemsOwner ≡ 185
provisioningClaimUsesRef185 = refl

gdpClaimAdequateForDescriptiveSynthesis :
  Claims.AdequateFor Claims.gdp15000Realization Claims.descriptiveSynthesisConsumer
gdpClaimAdequateForDescriptiveSynthesis = Claims.gdp15000Descriptive

gdpClaimNotCausalAuthority :
  Claims.AdequateFor Claims.gdp15000Realization Claims.causalMechanismConsumer → ⊥
gdpClaimNotCausalAuthority = Claims.gdp15000ReceiptDoesNotBecomeCausalThreshold

technologyScenarioNotCausalAuthority :
  Claims.AdequateFor Claims.optimisticTechnologyProjectionRealization
    Claims.causalMechanismConsumer → ⊥
technologyScenarioNotCausalAuthority = Claims.scenarioReceiptDoesNotBecomeObservation

policySynthesisNotPoliticalMandate :
  Claims.AdequateFor Claims.policyPackageSynthesisRealization
    Claims.politicalProgrammeConsumer → ⊥
policySynthesisNotPoliticalMandate = Claims.policySynthesisDoesNotSelfAuthorizeProgramme

reviewSynthesisStillDoesNotSelfAuthorizeCausation :
  Routing.Authorizes Routing.kallisReviewAuthority Routing.causalInterpretation → ⊥
reviewSynthesisStillDoesNotSelfAuthorizeCausation =
  Routing.kallisReviewAloneDoesNotAuthorizeCausalInterpretation
