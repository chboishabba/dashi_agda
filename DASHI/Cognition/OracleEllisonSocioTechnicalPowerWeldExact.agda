module DASHI.Cognition.OracleEllisonSocioTechnicalPowerWeldExact where

------------------------------------------------------------------------
-- SOCIO-TECHNICAL POWER WELD
--
-- The existing governance theorem says that a coarse service/technology
-- surface cannot recover the underlying power topology.  This owner reuses
-- that theorem for the Oracle/Ellison case without turning a synthetic assay
-- into a historical fact claim.
--
-- Case reading:
--   technology / vendor / declared defense posture
--     != institutional authority
--     != sovereign controller
--     != policy authorship
--     != personal motive.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Governance.SocioTechnicalPowerSelectionAssayExact as Power
import DASHI.Cognition.OracleEllisonTranscriptClaimAtlasExact as Claims
import DASHI.Cognition.OracleEllisonChinaIsraelComparativeFibreExact as Compare

------------------------------------------------------------------------
-- Literal master-owner reuse.
------------------------------------------------------------------------

sameServiceDoesNotDeterminePowerTopology :
  Power.SocioTechnicalPowerSelectionBoundary.sameServiceMeansSamePower
    Power.canonicalSocioTechnicalPowerSelectionBoundary
  ≡ false
sameServiceDoesNotDeterminePowerTopology =
  Power.SocioTechnicalPowerSelectionBoundary.sameServiceMeansSamePowerIsFalse
    Power.canonicalSocioTechnicalPowerSelectionBoundary

syntheticPowerAssayDoesNotProveHistoricalCase :
  Power.SocioTechnicalPowerSelectionBoundary.syntheticAssayProvesHistoricalCase
    Power.canonicalSocioTechnicalPowerSelectionBoundary
  ≡ false
syntheticPowerAssayDoesNotProveHistoricalCase =
  Power.SocioTechnicalPowerSelectionBoundary.syntheticAssayProvesHistoricalCaseIsFalse
    Power.canonicalSocioTechnicalPowerSelectionBoundary

------------------------------------------------------------------------
-- Case-specific non-promotions.
------------------------------------------------------------------------

technologyServiceSurfacePaysPowerTopology : Bool
technologyServiceSurfacePaysPowerTopology = false

reportedPersonalRelationshipPaysPolicyControl : Bool
reportedPersonalRelationshipPaysPolicyControl = false

corporateDefenseOrientationPaysSovereignController : Bool
corporateDefenseOrientationPaysSovereignController = false

corporateDefenseOrientationPaysSpecificIsraeliPolicyAuthorship : Bool
corporateDefenseOrientationPaysSpecificIsraeliPolicyAuthorship = false

operationalIntegrationPaysNeutralVendor : Bool
operationalIntegrationPaysNeutralVendor = false

operationalIntegrationPaysSovereignController : Bool
operationalIntegrationPaysSovereignController = false

sameVendorPaysSamePowerTopology : Bool
sameVendorPaysSamePowerTopology = false

------------------------------------------------------------------------
-- Positive scope: the new evidence is relevant rather than inert, but it
-- changes the graph by adding coordinates instead of collapsing coordinates.
------------------------------------------------------------------------

reportedRelationshipIsRelevantContextCoordinate : Bool
reportedRelationshipIsRelevantContextCoordinate = true

corporateDefenseOrientationIsRelevantContextCoordinate : Bool
corporateDefenseOrientationIsRelevantContextCoordinate = true

operationalDeploymentIsRelevantPowerCoordinate : Bool
operationalDeploymentIsRelevantPowerCoordinate = true

sameVendorAuthorityNonCollapse :
  Compare.sameVendorImpliesSameInstitutionalAuthority ≡ false
sameVendorAuthorityNonCollapse = refl

record OracleEllisonSocioTechnicalPowerBoundary : Set where
  constructor oracle-ellison-socio-technical-power-boundary
  field
    serviceDoesNotRecoverPower : Bool
    relationshipDoesNotCreatePolicyControl : Bool
    defensePostureDoesNotCreateSovereignController : Bool
    deploymentDoesNotCreateNeutrality : Bool
    deploymentDoesNotCreateSovereignControl : Bool
    relationshipContextIsRelevant : Bool
    defensePostureContextIsRelevant : Bool
    deploymentPowerContextIsRelevant : Bool
    syntheticAssayIsNotHistoricalEvidence : Bool

canonicalOracleEllisonSocioTechnicalPowerBoundary :
  OracleEllisonSocioTechnicalPowerBoundary
canonicalOracleEllisonSocioTechnicalPowerBoundary =
  oracle-ellison-socio-technical-power-boundary
    false false false false false true true true false
