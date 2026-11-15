module DASHI.Cognition.OracleEllisonSocioTechnicalPowerWeldExact where

------------------------------------------------------------------------
-- SOCIO-TECHNICAL POWER / EVIDENCE-GENEALOGY WELD
--
-- Two merged governance owners are reused here:
--
-- 1. a coarse service/technology surface cannot recover power topology;
-- 2. evidence genealogy remains edge-local, and even strong continuity does
--    not manufacture a universal coordinated network or central command.
--
-- Case reading:
--   technology / vendor / declared defense posture / reported relationship
--     != institutional authority
--     != sovereign controller
--     != policy authorship
--     != personal motive
--     != universal coordinated network.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Governance.SocioTechnicalPowerSelectionAssayExact as Power
import DASHI.Governance.EvidenceGradedGenealogyCore as Genealogy
import DASHI.Cognition.OracleEllisonTranscriptClaimAtlasExact as Claims
import DASHI.Cognition.OracleEllisonChinaIsraelComparativeFibreExact as Compare

------------------------------------------------------------------------
-- Literal master-owner reuse: socio-technical power.
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
-- Literal master-owner reuse: evidence-graded genealogy.
------------------------------------------------------------------------

genealogyProvenanceRemainsEdgeLocal :
  Genealogy.EvidenceGradedGenealogyBoundary.pathProvenanceRemainsEdgeLocal
    Genealogy.canonicalEvidenceGradedGenealogyBoundary
  ≡ true
genealogyProvenanceRemainsEdgeLocal = refl

genealogyContinuityDoesNotEqualCentralCommand :
  Genealogy.EvidenceGradedGenealogyBoundary.historicalContinuityEqualsCentralCommand
    Genealogy.canonicalEvidenceGradedGenealogyBoundary
  ≡ false
genealogyContinuityDoesNotEqualCentralCommand = refl

oneStrongEdgeDoesNotPayUniversalNetwork :
  Genealogy.OneStrongEdgeEstablishesUniversalNetwork → ⊥
oneStrongEdgeDoesNotPayUniversalNetwork =
  Genealogy.oneStrongEdgeDoesNotEstablishUniversalNetwork

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

documentedLinksPayUniversalCoordinatedNetwork : Bool
documentedLinksPayUniversalCoordinatedNetwork = false

historicalContinuityPaysCentralCommand : Bool
historicalContinuityPaysCentralCommand = false

relationshipPlusDefensePosturePaysCommonIdeology : Bool
relationshipPlusDefensePosturePaysCommonIdeology = false

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

multipleEdgesRemainIndividuallyProvenanced : Bool
multipleEdgesRemainIndividuallyProvenanced = true

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
    documentedLinksDoNotCreateUniversalNetwork : Bool
    continuityDoesNotCreateCentralCommand : Bool
    relationshipContextIsRelevant : Bool
    defensePostureContextIsRelevant : Bool
    deploymentPowerContextIsRelevant : Bool
    edgeLocalProvenanceRetained : Bool
    syntheticAssayIsNotHistoricalEvidence : Bool

canonicalOracleEllisonSocioTechnicalPowerBoundary :
  OracleEllisonSocioTechnicalPowerBoundary
canonicalOracleEllisonSocioTechnicalPowerBoundary =
  oracle-ellison-socio-technical-power-boundary
    false false false false false false false
    true true true true false
