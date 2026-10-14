module DASHI.Cognition.OracleEllisonAuthorityChainMaxCutExact where

------------------------------------------------------------------------
-- SAME-OBJECT AUTHORITY / CONTROL-ALLOCATION MAX-CUT
--
-- Primary product evidence pays a stronger proposition than mere deployment:
-- FIRE WEAVER has an explicit human control-allocation architecture.  The
-- Attack Officer configures autonomy/safety/time limits and can approve,
-- decline or re-program a system-selected fire solution.
--
-- Oracle's primary announcement separately pays that the same named product is
-- available on OCI.  The composition is product-identity level only: it does
-- not prove that a particular Israeli sovereign FIRE WEAVER deployment runs on
-- OCI, that Oracle occupies the Attack Officer role, or that Oracle authors
-- Israeli rules of engagement / sovereign policy.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Source coordinates.
------------------------------------------------------------------------

data AuthoritySource : Set where
  rafaelFireWeaverPrimaryBrochure : AuthoritySource
  oracleRafaelOCIPrimaryAnnouncement : AuthoritySource
  israelMODInstitutionalResponsibility : AuthoritySource

sourceLocator : AuthoritySource → String
sourceLocator rafaelFireWeaverPrimaryBrochure =
  "RAFAEL, FIRE WEAVER primary product brochure: Fire Management Terminal human-control allocation"
sourceLocator oracleRafaelOCIPrimaryAnnouncement =
  "Oracle News, 2024-09-10: RAFAEL IMILITE and FIRE WEAVER available on OCI for defense missions"
sourceLocator israelMODInstitutionalResponsibility =
  "Israel Ministry of Defense About Us: policy/procurement/industry responsibilities distinguished from IDF operational/technical responsibilities"

------------------------------------------------------------------------
-- Authority-chain stages.
------------------------------------------------------------------------

data AuthorityStage : Set where
  vendorCapability : AuthorityStage
  productDeploymentIntegration : AuthorityStage
  systemControlAllocation : AuthorityStage
  institutionalOperationalAuthority : AuthorityStage
  policyAuthorship : AuthorityStage
  sovereignControl : AuthorityStage

record AuthorityEdge : Set where
  constructor authority-edge
  field
    from to : AuthorityStage
    paid : Bool
    source : AuthoritySource
    boundedClaim : String

ociToFireWeaverIntegration : AuthorityEdge
ociToFireWeaverIntegration = authority-edge
  vendorCapability
  productDeploymentIntegration
  true
  oracleRafaelOCIPrimaryAnnouncement
  "OCI is a supported deployment substrate for the named RAFAEL FIRE WEAVER product."

fireWeaverControlAllocation : AuthorityEdge
fireWeaverControlAllocation = authority-edge
  productDeploymentIntegration
  systemControlAllocation
  true
  rafaelFireWeaverPrimaryBrochure
  "FIRE WEAVER exposes human-configured autonomy and Attack-Officer approve/decline/re-program authority over generated fire solutions."

controlAllocationToIsraeliInstitutionalAuthority : AuthorityEdge
controlAllocationToIsraeliInstitutionalAuthority = authority-edge
  systemControlAllocation
  institutionalOperationalAuthority
  false
  israelMODInstitutionalResponsibility
  "Institutional-role material distinguishes state responsibilities, but the acquired sources do not identify the operator/authority of a same-object Israeli OCI-hosted FIRE WEAVER instance."

institutionalAuthorityToPolicyAuthorship : AuthorityEdge
institutionalAuthorityToPolicyAuthorship = authority-edge
  institutionalOperationalAuthority
  policyAuthorship
  false
  israelMODInstitutionalResponsibility
  "Operational or technical authority does not by itself identify policy authorship."

policyAuthorshipToSovereignControl : AuthorityEdge
policyAuthorshipToSovereignControl = authority-edge
  policyAuthorship
  sovereignControl
  false
  israelMODInstitutionalResponsibility
  "No acquired same-object receipt identifies Oracle as final Israeli sovereign controller."

------------------------------------------------------------------------
-- Source-paid positive surface.
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
-- Non-promotions.
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

authorityChainClosedToSovereignControl : Bool
authorityChainClosedToSovereignControl = false

------------------------------------------------------------------------
-- Boundary receipt.
------------------------------------------------------------------------

record AuthorityChainBoundary : Set where
  constructor authority-chain-boundary
  field
    productArchitectureCanPayControlAllocation : Bool
    vendorHostingEqualsHumanOperator : Bool
    sameProductEqualsSameSovereignInstance : Bool
    operationalAuthorityEqualsPolicyAuthorship : Bool
    policyAuthorshipAutomaticallyEqualsSovereignControl : Bool
    eachAuthorityHopRequiresSameObjectReceipt : Bool

canonicalAuthorityChainBoundary : AuthorityChainBoundary
canonicalAuthorityChainBoundary =
  authority-chain-boundary true false false false false true
