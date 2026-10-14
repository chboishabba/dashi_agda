module DASHI.Cognition.OracleEllisonAuthorityChainMaxCutExact where

------------------------------------------------------------------------
-- SAME-PRODUCT AUTHORITY / CONTROL-ALLOCATION MAX-CUT
--
-- FIRE WEAVER now has three separately sourced surfaces:
--
--   1. product architecture / human control allocation;
--   2. an IDF/IMOD acquisition, development and operational-authority branch;
--   3. an Oracle/RAFAEL OCI deployment-capability branch.
--
-- The branches share a named product identity.  The acquired sources do NOT
-- establish that the operational IDF deployment is the same runtime instance
-- as an OCI-hosted deployment.  Product identity therefore cannot silently
-- close the instance join.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Cognition.OracleEllisonCapabilityPromotionExact as Promotion

------------------------------------------------------------------------
-- Source coordinates.
------------------------------------------------------------------------

data AuthoritySource : Set where
  rafaelFireWeaverPrimaryBrochure : AuthoritySource
  oracleRafaelOCIPrimaryAnnouncement : AuthoritySource
  rafaelIDFAcquisitionAnnouncement2020 : AuthoritySource
  janesIDFFireWeaverOperationalAuthority : AuthoritySource
  israelMODInstitutionalResponsibility : AuthoritySource

sourceLocator : AuthoritySource → String
sourceLocator rafaelFireWeaverPrimaryBrochure =
  "RAFAEL FIRE WEAVER primary brochure: Fire Management Terminal human-control allocation"
sourceLocator oracleRafaelOCIPrimaryAnnouncement =
  "Oracle News 2024-09-10: RAFAEL IMILITE and FIRE WEAVER available on OCI for defense missions"
sourceLocator rafaelIDFAcquisitionAnnouncement2020 =
  "RAFAEL/IMOD acquisition announcement, 2020: IDF acquisition; joint IDF Ground Forces + DDR&D + RAFAEL development; Ground Forces division deployment purpose"
sourceLocator janesIDFFireWeaverOperationalAuthority =
  "Janes Fire Weaver operational report: brigade deployment, battalion-command-post engagement approval and dual-custody operator approval"
sourceLocator israelMODInstitutionalResponsibility =
  "Israel Ministry of Defense institutional responsibility surface: ministry policy/procurement/industry roles remain distinct from IDF operational/technical roles"

------------------------------------------------------------------------
-- Authority stages and object scopes.
------------------------------------------------------------------------

data AuthorityStage : Set where
  vendorCapability : AuthorityStage
  productDeploymentIntegration : AuthorityStage
  systemControlAllocation : AuthorityStage
  institutionalOperationalAuthority : AuthorityStage
  policyAuthorship : AuthorityStage
  sovereignControl : AuthorityStage

data AuthorityObjectScope : Set where
  fireWeaverProductArchitecture : AuthorityObjectScope
  ociFireWeaverDeploymentCapability : AuthorityObjectScope
  idfFireWeaverOperationalDeployment : AuthorityObjectScope
  specificIDFOCIHostedInstance : AuthorityObjectScope

record AuthorityEdge : Set where
  constructor authority-edge
  field
    scope : AuthorityObjectScope
    from to : AuthorityStage
    paid : Bool
    source : AuthoritySource
    boundedClaim : String

------------------------------------------------------------------------
-- Product / OCI branch.
------------------------------------------------------------------------

ociToFireWeaverIntegration : AuthorityEdge
ociToFireWeaverIntegration = authority-edge
  ociFireWeaverDeploymentCapability
  vendorCapability
  productDeploymentIntegration
  true
  oracleRafaelOCIPrimaryAnnouncement
  "OCI is a supported deployment substrate for the named RAFAEL FIRE WEAVER product."

fireWeaverControlAllocation : AuthorityEdge
fireWeaverControlAllocation = authority-edge
  fireWeaverProductArchitecture
  productDeploymentIntegration
  systemControlAllocation
  true
  rafaelFireWeaverPrimaryBrochure
  "FIRE WEAVER exposes human-configured autonomy and Attack-Officer approve/decline/re-program authority over generated fire solutions."

------------------------------------------------------------------------
-- IDF / IMOD operational branch.
------------------------------------------------------------------------

idfAcquisitionToOperationalDeployment : AuthorityEdge
idfAcquisitionToOperationalDeployment = authority-edge
  idfFireWeaverOperationalDeployment
  productDeploymentIntegration
  institutionalOperationalAuthority
  true
  rafaelIDFAcquisitionAnnouncement2020
  "IMOD announced IDF acquisition and an IDF Ground Forces deployment programme for FIRE WEAVER."

idfOperationalControlAllocation : AuthorityEdge
idfOperationalControlAllocation = authority-edge
  idfFireWeaverOperationalDeployment
  systemControlAllocation
  institutionalOperationalAuthority
  true
  janesIDFFireWeaverOperationalAuthority
  "Operational reporting places engagement approval in an IDF battalion command post and requires operator agreement before firing."

institutionalAuthorityToPolicyAuthorship : AuthorityEdge
institutionalAuthorityToPolicyAuthorship = authority-edge
  idfFireWeaverOperationalDeployment
  institutionalOperationalAuthority
  policyAuthorship
  false
  israelMODInstitutionalResponsibility
  "Operational authority over FIRE WEAVER does not by itself identify authorship of the governing rules, policy or doctrine."

policyAuthorshipToSovereignControl : AuthorityEdge
policyAuthorshipToSovereignControl = authority-edge
  idfFireWeaverOperationalDeployment
  policyAuthorship
  sovereignControl
  false
  israelMODInstitutionalResponsibility
  "No acquired same-object receipt makes Oracle the final sovereign decision authority over the IDF deployment."

------------------------------------------------------------------------
-- Source-paid product architecture.
------------------------------------------------------------------------

fireWeaverHumanControlAllocationPaid : Bool
fireWeaverHumanControlAllocationPaid = true

fireWeaverAttackOfficerCanSetAutonomy : Bool
fireWeaverAttackOfficerCanSetAutonomy = true

fireWeaverAttackOfficerCanSetSafetyZones : Bool
fireWeaverAttackOfficerCanSetSafetyZones = true

fireWeaverAttackOfficerOverridePaid : Bool
fireWeaverAttackOfficerOverridePaid = true

fireWeaverSystemSelectsCandidateFireSolution : Bool
fireWeaverSystemSelectsCandidateFireSolution = true

fireWeaverSameNamedProductAvailableOnOCI : Bool
fireWeaverSameNamedProductAvailableOnOCI = true

------------------------------------------------------------------------
-- Newly paid IDF/IMOD authority surface.
------------------------------------------------------------------------

idfFireWeaverAcquisitionPaid : Bool
idfFireWeaverAcquisitionPaid = true

idfGroundForcesJointDevelopmentPaid : Bool
idfGroundForcesJointDevelopmentPaid = true

idfGroundForcesOperationalAuthorityPaid : Bool
idfGroundForcesOperationalAuthorityPaid = true

idfBattalionCommandPostEngagementApprovalPaid : Bool
idfBattalionCommandPostEngagementApprovalPaid = true

idfDualCustodyEngagementApprovalPaid : Bool
idfDualCustodyEngagementApprovalPaid = true

------------------------------------------------------------------------
-- Claim-relative promotion lattice weld.
--
-- L3 is paid both for the product's control architecture and for the bounded
-- IDF operational authority surface. Oracle's relation to the product remains
-- L2 because OCI integration does not make Oracle the human operator, IDF
-- command authority, policy author or sovereign controller.
------------------------------------------------------------------------

fireWeaverProductArchitectureHighestPaidLevel : Promotion.PromotionLevel
fireWeaverProductArchitectureHighestPaidLevel = Promotion.systemArchitectureControl

idfFireWeaverOperationalAuthorityHighestPaidLevel : Promotion.PromotionLevel
idfFireWeaverOperationalAuthorityHighestPaidLevel = Promotion.systemArchitectureControl

oracleRafaelRelationshipHighestPaidLevel : Promotion.PromotionLevel
oracleRafaelRelationshipHighestPaidLevel = Promotion.operationalIntegration

------------------------------------------------------------------------
-- The critical deployment-instance fork.
------------------------------------------------------------------------

idfDeploymentIsOCIHostedSameInstancePaid : Bool
idfDeploymentIsOCIHostedSameInstancePaid = false

sharedProductIdentityClosesDeploymentInstanceJoin : Bool
sharedProductIdentityClosesDeploymentInstanceJoin = false

record DeploymentInstanceJoinReceipt : Set where
  constructor deployment-instance-join-receipt
  field
    idfDeploymentReference : String
    ociDeploymentReference : String
    sameRuntimeInstanceReference : String

-- No canonical inhabitant is supplied: that would require a source explicitly
-- identifying the operational IDF instance as the OCI-hosted instance.

------------------------------------------------------------------------
-- Remaining non-promotions.
------------------------------------------------------------------------

oracleControlsFireWeaverAttackOfficer : Bool
oracleControlsFireWeaverAttackOfficer = false

oracleAuthorsFireWeaverRulesOfEngagement : Bool
oracleAuthorsFireWeaverRulesOfEngagement = false

israeliSovereignOCIInstanceControlPaid : Bool
israeliSovereignOCIInstanceControlPaid = false

sameProductIdentityProvesSameDeploymentInstance : Bool
sameProductIdentityProvesSameDeploymentInstance = false

productControlArchitectureProvesPolicyAuthorship : Bool
productControlArchitectureProvesPolicyAuthorship = false

fireWeaverPolicyAuthorshipPaid : Bool
fireWeaverPolicyAuthorshipPaid = false

authorityChainClosedToSovereignControl : Bool
authorityChainClosedToSovereignControl = false

------------------------------------------------------------------------
-- Boundary receipt.
------------------------------------------------------------------------

record AuthorityChainBoundary : Set where
  constructor authority-chain-boundary
  field
    productArchitectureCanPayControlAllocation : Bool
    idfOperationalAuthorityCanBeSourcePaid : Bool
    vendorHostingEqualsHumanOperator : Bool
    sameProductEqualsSameSovereignInstance : Bool
    operationalAuthorityEqualsPolicyAuthorship : Bool
    policyAuthorshipAutomaticallyEqualsSovereignControl : Bool
    eachAuthorityHopRequiresSameObjectReceipt : Bool

canonicalAuthorityChainBoundary : AuthorityChainBoundary
canonicalAuthorityChainBoundary =
  authority-chain-boundary true true false false false false true
