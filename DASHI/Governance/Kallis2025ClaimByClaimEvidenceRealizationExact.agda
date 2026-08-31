module DASHI.Governance.Kallis2025ClaimByClaimEvidenceRealizationExact where

open import DASHI.Core.Prelude
import DASHI.Governance.Kallis2025ClaimAuthorityRoutingExact as Routing
import DASHI.Governance.Kallis2025EvidenceAtlasExact as Atlas

------------------------------------------------------------------------
-- KALLIS ET AL. 2025: CLAIM-BY-CLAIM EVIDENCE REALIZATION
--
-- This module turns the section-level evidence atlas into explicit review-claim
-- records.  A claim carries its upstream atlas anchor, intended consumer and
-- residual status.  The finite constructors below are routing receipts only;
-- they do not strengthen the evidence class attached by the review/source.
------------------------------------------------------------------------

data ReviewClaim : Set where
  materialFootprintCouplingClaim
  materialDecouplingReviewClaim
  optimisticTechnologyProjectionClaim
  postGrowthMitigationScenarioClaim
  lowGrowCanadaClaim
  eurogreenFranceClaim
  workingTimeCarbonAssociationClaim
  policyPackageSynthesisClaim
  growthDependencyClaim
  provisioningSystemsClaim
  lowEnergyNeedSatisfactionClaim
  unequalExchangeClaim
  postDevelopmentClaim
  gdp15000Claim
  : ReviewClaim

data ClaimConsumer : Set where
  descriptiveSynthesisConsumer
  scenarioInterpretationConsumer
  causalMechanismConsumer
  policyDesignConsumer
  politicalProgrammeConsumer
  : ClaimConsumer

data LiveResidual : Set where
  associationNotCausation
  scenarioNotObservation
  reviewNotMandate
  distributionStillOpen
  politicalTransitionStillOpen
  noAdditionalResidualRecorded
  : LiveResidual

record ClaimEvidenceRealization : Set where
  constructor claimEvidenceRealization
  field
    claim : ReviewClaim
    anchor : Atlas.EvidenceAnchor
    consumer : ClaimConsumer
    residual : LiveResidual

materialFootprintCouplingRealization : ClaimEvidenceRealization
materialFootprintCouplingRealization =
  claimEvidenceRealization materialFootprintCouplingClaim Atlas.materialFootprintCoupling
    descriptiveSynthesisConsumer associationNotCausation

materialDecouplingReviewRealization : ClaimEvidenceRealization
materialDecouplingReviewRealization =
  claimEvidenceRealization materialDecouplingReviewClaim Atlas.materialDecouplingReview
    descriptiveSynthesisConsumer reviewNotMandate

optimisticTechnologyProjectionRealization : ClaimEvidenceRealization
optimisticTechnologyProjectionRealization =
  claimEvidenceRealization optimisticTechnologyProjectionClaim Atlas.optimisticTechnologyProjection
    scenarioInterpretationConsumer scenarioNotObservation

postGrowthMitigationScenarioRealization : ClaimEvidenceRealization
postGrowthMitigationScenarioRealization =
  claimEvidenceRealization postGrowthMitigationScenarioClaim Atlas.postGrowthMitigationScenario
    scenarioInterpretationConsumer scenarioNotObservation

lowGrowCanadaRealization : ClaimEvidenceRealization
lowGrowCanadaRealization =
  claimEvidenceRealization lowGrowCanadaClaim Atlas.lowGrowCanada
    scenarioInterpretationConsumer scenarioNotObservation

eurogreenFranceRealization : ClaimEvidenceRealization
neurogreenFranceRealization =
  claimEvidenceRealization eurogreenFranceClaim Atlas.neurogreenFrance
    scenarioInterpretationConsumer scenarioNotObservation

workingTimeCarbonAssociationRealization : ClaimEvidenceRealization
workingTimeCarbonAssociationRealization =
  claimEvidenceRealization workingTimeCarbonAssociationClaim Atlas.workingTimeCarbonAssociation
    descriptiveSynthesisConsumer associationNotCausation

policyPackageSynthesisRealization : ClaimEvidenceRealization
policyPackageSynthesisRealization =
  claimEvidenceRealization policyPackageSynthesisClaim Atlas.policyPackageSynthesis
    policyDesignConsumer reviewNotMandate

growthDependencyRealization : ClaimEvidenceRealization
growthDependencyRealization =
  claimEvidenceRealization growthDependencyClaim Atlas.growthDependencyCaseStudy
    descriptiveSynthesisConsumer associationNotCausation

provisioningSystemsRealization : ClaimEvidenceRealization
provisioningSystemsRealization =
  claimEvidenceRealization provisioningSystemsClaim Atlas.provisioningSystemsOwner
    descriptiveSynthesisConsumer associationNotCausation

lowEnergyNeedSatisfactionRealization : ClaimEvidenceRealization
lowEnergyNeedSatisfactionRealization =
  claimEvidenceRealization lowEnergyNeedSatisfactionClaim Atlas.lowEnergyNeedSatisfactionOwner
    descriptiveSynthesisConsumer associationNotCausation

unequalExchangeRealization : ClaimEvidenceRealization
unequalExchangeRealization =
  claimEvidenceRealization unequalExchangeClaim Atlas.unequalExchangeOwner
    descriptiveSynthesisConsumer distributionStillOpen

postDevelopmentRealization : ClaimEvidenceRealization
postDevelopmentRealization =
  claimEvidenceRealization postDevelopmentClaim Atlas.postDevelopmentOwner
    descriptiveSynthesisConsumer politicalTransitionStillOpen

gdp15000Realization : ClaimEvidenceRealization
gdp15000Realization =
  claimEvidenceRealization gdp15000Claim Atlas.gdp15000Owner
    descriptiveSynthesisConsumer associationNotCausation

------------------------------------------------------------------------
-- Consumer / evidence-class promotion boundaries.
------------------------------------------------------------------------

data AdequateFor : ClaimEvidenceRealization → ClaimConsumer → Set where
  materialFootprintDescriptive :
    AdequateFor materialFootprintCouplingRealization descriptiveSynthesisConsumer
  materialReviewDescriptive :
    AdequateFor materialDecouplingReviewRealization descriptiveSynthesisConsumer
  optimisticScenarioInterpretation :
    AdequateFor optimisticTechnologyProjectionRealization scenarioInterpretationConsumer
  mitigationScenarioInterpretation :
    AdequateFor postGrowthMitigationScenarioRealization scenarioInterpretationConsumer
  lowGrowScenarioInterpretation :
    AdequateFor lowGrowCanadaRealization scenarioInterpretationConsumer
  eurogreenScenarioInterpretation :
    AdequateFor neurogreenFranceRealization scenarioInterpretationConsumer
  workingTimeDescriptive :
    AdequateFor workingTimeCarbonAssociationRealization descriptiveSynthesisConsumer
  provisioningDescriptive :
    AdequateFor provisioningSystemsRealization descriptiveSynthesisConsumer
  lowEnergyDescriptive :
    AdequateFor lowEnergyNeedSatisfactionRealization descriptiveSynthesisConsumer
  unequalExchangeDescriptive :
    AdequateFor unequalExchangeRealization descriptiveSynthesisConsumer
  gdp15000Descriptive :
    AdequateFor gdp15000Realization descriptiveSynthesisConsumer

scenarioReceiptDoesNotBecomeObservation :
  AdequateFor optimisticTechnologyProjectionRealization causalMechanismConsumer → ⊥
scenarioReceiptDoesNotBecomeObservation ()

gdp15000ReceiptDoesNotBecomeCausalThreshold :
  AdequateFor gdp15000Realization causalMechanismConsumer → ⊥
gdp15000ReceiptDoesNotBecomeCausalThreshold ()

policySynthesisDoesNotSelfAuthorizeProgramme :
  AdequateFor policyPackageSynthesisRealization politicalProgrammeConsumer → ⊥
policySynthesisDoesNotSelfAuthorizeProgramme ()

record ClaimByClaimEvidenceBoundary : Set where
  constructor claimByClaimEvidenceBoundary
  field
    sameReviewIdentityMakesEvidenceClassesEqual : Bool
    sameReviewIdentityMakesEvidenceClassesEqualIsFalse :
      sameReviewIdentityMakesEvidenceClassesEqual ≡ false
    modelScenarioBecomesHistoricalObservation : Bool
    modelScenarioBecomesHistoricalObservationIsFalse :
      modelScenarioBecomesHistoricalObservation ≡ false
    empiricalAssociationBecomesCausalMechanism : Bool
    empiricalAssociationBecomesCausalMechanismIsFalse :
      empiricalAssociationBecomesCausalMechanism ≡ false
    reviewPolicySynthesisBecomesPoliticalMandate : Bool
    reviewPolicySynthesisBecomesPoliticalMandateIsFalse :
      reviewPolicySynthesisBecomesPoliticalMandate ≡ false
    claimRealizationCarriesResidualStatus : Bool
    claimRealizationCarriesResidualStatusIsTrue :
      claimRealizationCarriesResidualStatus ≡ true

canonicalClaimByClaimEvidenceBoundary : ClaimByClaimEvidenceBoundary
canonicalClaimByClaimEvidenceBoundary =
  claimByClaimEvidenceBoundary false refl false refl false refl false refl true refl
