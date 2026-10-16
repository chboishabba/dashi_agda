module DASHI.Cognition.VilyaProtectionSourceAtlasExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Cognition.ProtectiveSpatialIntelligenceExact as Core

------------------------------------------------------------------------
-- VILYA SOURCE-BOUNDED PRODUCT SURFACE
--
-- Public product/developer material pays product-description claims only.
-- It does not independently validate geometry accuracy, threat-score quality,
-- causal prevention, operator performance or institutional deployment.
------------------------------------------------------------------------

data VilyaSource : Set where
  vilyaProductSite : VilyaSource
  vilyaFAQ : VilyaSource
  dfieldCaseStudy : VilyaSource

sourceLocator : VilyaSource → String
sourceLocator vilyaProductSite =
  "VILYA product site, accessed 2026-10-16: interactive 3D intelligence for police, counter-terror and close protection"
sourceLocator vilyaFAQ =
  "VILYA FAQ, accessed 2026-10-16: venue, threat, camera, route, live and report workflow"
sourceLocator dfieldCaseStudy =
  "DField Solutions VILYA case study: assassination-prevention software platform description"

data VendorClaimKind : Set where
  realWorld3DGeometry : VendorClaimKind
  ownershipAndBuildingIntel : VendorClaimKind
  rooftopSightlineAssessment : VendorClaimKind
  cameraCoverageAndDeadZones : VendorClaimKind
  routeAndZonePlanning : VendorClaimKind
  liveOperatorTracking : VendorClaimKind
  fusedOpenSourceIntel : VendorClaimKind
  missionBriefing : VendorClaimKind
  assassinationPreventionPositioning : VendorClaimKind

record VendorClaimReceipt : Set where
  constructor vendor-claim-receipt
  field
    claimKind : VendorClaimKind
    source : VilyaSource
    boundedClaim : String
    vendorDescriptionPaid : Bool
    independentValidationPaid : Bool

open VendorClaimReceipt public

sightlineClaim : VendorClaimReceipt
sightlineClaim = vendor-claim-receipt
  rooftopSightlineAssessment
  vilyaFAQ
  "The vendor describes floor-by-floor rooftop sightline analysis over real-height geometry."
  true false

cameraClaim : VendorClaimReceipt
cameraClaim = vendor-claim-receipt
  cameraCoverageAndDeadZones
  vilyaFAQ
  "The vendor describes camera coverage cones and dead-zone visualisation on the 3D model."
  true false

fusionClaim : VendorClaimReceipt
fusionClaim = vendor-claim-receipt
  fusedOpenSourceIntel
  vilyaProductSite
  "The vendor describes cameras, weather, transport and open-source intelligence fused into one spatial picture."
  true false

------------------------------------------------------------------------
-- Five-stage public workflow.
------------------------------------------------------------------------

data VilyaWorkflowStage : Set where
  understandSite : VilyaWorkflowStage
  assessThreat : VilyaWorkflowStage
  planMission : VilyaWorkflowStage
  monitorOperation : VilyaWorkflowStage
  briefTeam : VilyaWorkflowStage

stageConsumer : VilyaWorkflowStage → Core.ProtectiveConsumer
stageConsumer understandSite = Core.siteUnderstandingConsumer
stageConsumer assessThreat = Core.threatAssessmentConsumer
stageConsumer planMission = Core.missionPlanningConsumer
stageConsumer monitorOperation = Core.liveOperationsConsumer
stageConsumer briefTeam = Core.briefingAndReviewConsumer

fiveStageWorkflowPaid : Bool
fiveStageWorkflowPaid = true

vendorDescriptionCreatesIndependentPerformanceValidation : Bool
vendorDescriptionCreatesIndependentPerformanceValidation = false

vendorClaimCreatesOperationalDeploymentFact : Bool
vendorClaimCreatesOperationalDeploymentFact = false

vendorClaimCreatesCausalPreventionFact : Bool
vendorClaimCreatesCausalPreventionFact = false

vendorClaimCreatesLegalOrUseOfForceAuthority : Bool
vendorClaimCreatesLegalOrUseOfForceAuthority = false

------------------------------------------------------------------------
-- Current empirical residual.
------------------------------------------------------------------------

record VilyaValidationDemand : Set where
  constructor vilya-validation-demand
  field
    exactBuildReference : String
    exactVenueReference : String
    sourceGeometryReference : String
    groundTruthReference : String
    querySetReference : String
    measuredErrorReference : String
    operatorProtocolReference : String
    independentEvaluatorReference : String

-- No canonical inhabitant: public marketing material is not a validation run.

record VilyaSourceBoundary : Set where
  constructor vilya-source-boundary
  field
    workflowDescriptionPaid : Bool
    spatialCapabilityDescriptionPaid : Bool
    performanceValidated : Bool
    causalPreventionValidated : Bool
    deploymentIdentityValidated : Bool
    useOfForceAuthorityCreated : Bool

canonicalVilyaSourceBoundary : VilyaSourceBoundary
canonicalVilyaSourceBoundary =
  vilya-source-boundary true true false false false false
