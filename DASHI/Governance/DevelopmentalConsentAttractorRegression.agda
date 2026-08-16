module DASHI.Governance.DevelopmentalConsentAttractorRegression where

open import DASHI.Core.Prelude

import DASHI.Governance.GenericSocialAttractor as Generic
import DASHI.Governance.EpistemicAttractorDynamicsExact as Dynamics
import DASHI.Governance.CausalResolutionExact as Resolution
import DASHI.Governance.InterventionBundleExact as Intervention
import DASHI.Governance.DomainPermeabilityAuthorityTransport as Domain
import DASHI.Governance.ConsentDistrustDualityExact as Duality
import DASHI.Governance.DevelopmentalRegulationCoordinatesExact as Coordinates
import DASHI.Governance.WeightedEpistemicPipelineExact as Pipeline
import DASHI.Governance.SocialAttractorAdaptersExact as Adapters

------------------------------------------------------------------------
-- Focused local-kernel regression root for the theorem-producing tranche.
-- No CI assumption is encoded here; consumers can run:
--
--   agda -i . DASHI/Governance/DevelopmentalConsentAttractorRegression.agda
------------------------------------------------------------------------

genericFixedPointDoesNotApprove :
  Generic.GenericAttractorBoundary.fixedPointImpliesNormativeApproval
    Generic.canonicalGenericAttractorBoundary
  ≡ false
genericFixedPointDoesNotApprove = refl

stableDynamicsNeedsWitness :
  Dynamics.EpistemicDynamicsBoundary.stabilityRequiresDynamicsWitness
    Dynamics.canonicalEpistemicDynamicsBoundary
  ≡ true
stableDynamicsNeedsWitness = refl

causalCompressionCollisionLosesInjectivity :
  Resolution.CausalResolutionBoundary.collisionPreservesInjectiveResolution
    Resolution.canonicalCausalResolutionBoundary
  ≡ false
causalCompressionCollisionLosesInjectivity = refl

partialReformDoesNotRefuteSupportedBundle :
  Intervention.InterventionIdentificationBoundary.failedPartialReformRefutesSupportedReform
    Intervention.canonicalInterventionIdentificationBoundary
  ≡ false
partialReformDoesNotRefuteSupportedBundle = refl

domainReuseNeedsAuthorityWitness :
  Domain.DomainTransportReceipt.targetDomainNeedsOwnAuthorityWitness
    Domain.canonicalDomainTransportReceipt
  ≡ true
domainReuseNeedsAuthorityWitness = refl

distrustDoesNotProveReplacementAuthority :
  Duality.ConsentDistrustBoundary.distrustOfOneInstitutionProvesAnotherReliable
    Duality.canonicalConsentDistrustBoundary
  ≡ false
distrustDoesNotProveReplacementAuthority = refl

regulationCoordinatesRemainDistinct :
  Coordinates.RegulationCoordinateBoundary.sharedFeedbackTopologyEqualsSamePsychology
    Coordinates.canonicalRegulationCoordinateBoundary
  ≡ false
regulationCoordinatesRemainDistinct = refl

possiblePipelineStepIsNotProbabilityClaim :
  Pipeline.WeightedPipelineBoundary.genericWeightEqualsProbability
    Pipeline.canonicalWeightedPipelineBoundary
  ≡ false
possiblePipelineStepIsNotProbabilityClaim = refl

genericAdapterDoesNotCreateNormativeApproval :
  Adapters.SocialAttractorAdapterBoundary.genericFixedPointCreatesNormativeApproval
    Adapters.canonicalSocialAttractorAdapterBoundary
  ≡ false
genericAdapterDoesNotCreateNormativeApproval = refl

exactUnderprovisionedCountermodel :
  Intervention.evaluate Intervention.underprovisioned
  ≡ Intervention.fails
exactUnderprovisionedCountermodel = refl

exactSupportedCountermodel :
  Intervention.evaluate Intervention.supported
  ≡ Intervention.succeeds
exactSupportedCountermodel = refl
