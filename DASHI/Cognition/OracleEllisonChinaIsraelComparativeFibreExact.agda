module DASHI.Cognition.OracleEllisonChinaIsraelComparativeFibreExact where

------------------------------------------------------------------------
-- SAME VENDOR, DIFFERENT STATE / INSTITUTION / DEPLOYMENT FIBRES
--
-- The comparison preserves vendor identity while refusing to collapse
-- sovereign objective, institutional authority, deployment path or controller.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Cognition.OracleEllisonCapabilityPromotionExact as Promotion

data StateContext : Set where
  prcStateContext : StateContext
  israelStateContext : StateContext

data Institution : Set where
  prcPolice : Institution
  rafaelDefenseCompany : Institution
  israelGovernmentProcurement : Institution

data Vendor : Set where
  oracle : Vendor
  aws : Vendor
  google : Vendor

data TechnologyRole : Set where
  policeDatabaseInfrastructure : TechnologyRole
  defenseCloudInfrastructure : TechnologyRole
  publicGovernmentCloud : TechnologyRole

data DeploymentStatus : Set where
  reportedOperationalIntegration : DeploymentStatus
  officialVendorIntegration : DeploymentStatus
  selectedPrimeProvider : DeploymentStatus
  materiallyCounterevidencedPrimeProvider : DeploymentStatus

record DeploymentEdge : Set where
  constructor deployment-edge
  field
    state : StateContext
    institution : Institution
    vendor : Vendor
    role : TechnologyRole
    status : DeploymentStatus
    note : String

oracleChinaEdge : DeploymentEdge
oracleChinaEdge = deployment-edge
  prcStateContext
  prcPolice
  oracle
  policeDatabaseInfrastructure
  reportedOperationalIntegration
  "AP/CECC evidence places Oracle products in PRC police Golden Shield upgrade infrastructure; political objective and sovereign control remain PRC-state coordinates."

oracleRafaelEdge : DeploymentEdge
oracleRafaelEdge = deployment-edge
  israelStateContext
  rafaelDefenseCompany
  oracle
  defenseCloudInfrastructure
  officialVendorIntegration
  "Oracle/RAFAEL primary announcement places IMILITE and FIRE WEAVER on OCI for defense missions."

awsNimbusEdge : DeploymentEdge
awsNimbusEdge = deployment-edge
  israelStateContext
  israelGovernmentProcurement
  aws
  publicGovernmentCloud
  selectedPrimeProvider
  "Government Procurement Administration names AWS as a selected Nimbus cloud provider."

googleNimbusEdge : DeploymentEdge
googleNimbusEdge = deployment-edge
  israelStateContext
  israelGovernmentProcurement
  google
  publicGovernmentCloud
  selectedPrimeProvider
  "Government Procurement Administration names Google as a selected Nimbus cloud provider."

oracleNimbusEdge : DeploymentEdge
oracleNimbusEdge = deployment-edge
  israelStateContext
  israelGovernmentProcurement
  oracle
  publicGovernmentCloud
  materiallyCounterevidencedPrimeProvider
  "Oracle is not one of the selected prime Nimbus public-cloud providers in the official procurement record."

------------------------------------------------------------------------
-- Comparison boundary.
------------------------------------------------------------------------

sameVendorImpliesSameStateObjective : Bool
sameVendorImpliesSameStateObjective = false

sameVendorImpliesSameInstitutionalAuthority : Bool
sameVendorImpliesSameInstitutionalAuthority = false

sameVendorImpliesCommonController : Bool
sameVendorImpliesCommonController = false

sameVendorImpliesSameDeploymentMechanism : Bool
sameVendorImpliesSameDeploymentMechanism = false

operationalIntegrationImpliesNeutrality : Bool
operationalIntegrationImpliesNeutrality = false

operationalIntegrationImpliesSovereignControl : Bool
operationalIntegrationImpliesSovereignControl = false

record ComparativeFibreBoundary : Set where
  constructor comparative-fibre-boundary
  field
    vendorCanParticipateInMultipleStateSystems : Bool
    stateObjectiveRemainsSeparate : Bool
    institutionalAuthorityRemainsSeparate : Bool
    deploymentPathRemainsSeparate : Bool
    controllerIdentityRemainsSeparate : Bool

canonicalComparativeFibreBoundary : ComparativeFibreBoundary
canonicalComparativeFibreBoundary =
  comparative-fibre-boundary true true true true true
