module DASHI.Law.SensibLawAzureSpringfieldInducedGasDemandExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Law.SensibLawSpringfieldResidentialGasEndpointLockInExact as Endpoint
import DASHI.Law.SensibLawSpringfieldGasLobbyingOwnershipSnowballExact as Influence

------------------------------------------------------------------------
-- AZURE / SPRINGFIELD INDUCED-GAS-DEMAND INVESTIGATIVE OWNER
--
-- The operator has identified the observed dwelling as an Azure dwelling.
-- That same-object identity is retained as an operator observation until an
-- exact contract/title/building-approval/project-SPV document pays it.
--
-- The hypothesis under test is economic/technical rather than causal by fiat:
-- a dwelling may preserve a separate fossil-gas connection for a specialised
-- gas wok burner and instantaneous gas hot water even where substantial
-- electrical infrastructure and rooftop solar are also present.  That design
-- can create or preserve gas demand, fixed-customer revenue and throughput,
-- but it does not by itself prove lobbying, corruption, developer intent or a
-- beneficiary relationship.
------------------------------------------------------------------------

data SameObjectStatus : Set where
  operatorReportedSameObject : SameObjectStatus
  primaryDocumentPaid : SameObjectStatus
  unresolvedSameObject : SameObjectStatus

record DeveloperEndpointIdentity : Set where
  constructor developer-endpoint-identity
  field
    developerName : String
    endpointDescription : String
    status : SameObjectStatus
    exactAddressPublished : Bool
    exactAddressPublishedIsFalse : exactAddressPublished ≡ false
    primaryProjectDocumentPaid : Bool

open DeveloperEndpointIdentity public

azureDwellingIdentityObservation : DeveloperEndpointIdentity
azureDwellingIdentityObservation = developer-endpoint-identity
  "Azure Development Group"
  "De-identified observed Springfield-area dwelling with gas wok burner, instantaneous gas hot water, electrical cooking capacity and rooftop solar."
  operatorReportedSameObject
  false refl
  false

------------------------------------------------------------------------
-- Distinct demand mechanisms.  These must not be collapsed into one claim.
------------------------------------------------------------------------

data DemandMechanism : Set where
  separateGasConnectionRetention : DemandMechanism
  fixedCustomerChargeExposure : DemandMechanism
  gasThroughputOpportunity : DemandMechanism
  hotWaterDrawBeforeUsefulTemperature : DemandMechanism
  highHeatGasCookingCapability : DemandMechanism
  applianceReplacementLockIn : DemandMechanism
  networkAssetUtilisation : DemandMechanism

record DemandHypothesis : Set where
  constructor demand-hypothesis
  field
    mechanism : DemandMechanism
    statement : String
    paid : Bool
    requiredReceipt : String

open DemandHypothesis public

separateGasConnectionDemandResidual : DemandHypothesis
separateGasConnectionDemandResidual = demand-hypothesis
  separateGasConnectionRetention
  "A separate gas service can preserve household gas demand even when substantial electrical infrastructure and rooftop solar are present. The exact project specification and connection rationale remain unpaid."
  false
  "Exact Azure dwelling/project inclusions, hydraulic/gas drawings, electrical schedule, appliance schedule and MIRN/distributor record."

fixedCustomerRevenueResidual : DemandHypothesis
fixedCustomerRevenueResidual = demand-hypothesis
  fixedCustomerChargeExposure
  "A connected gas customer can contribute fixed network/customer revenue even at low throughput. The exact current Allgas tariff applicable to the endpoint and the endpoint's distributor/retailer identity remain to be bound."
  false
  "Current applicable Allgas/AER tariff schedule plus exact endpoint distributor and connection status."

throughputBenefitResidual : DemandHypothesis
throughputBenefitResidual = demand-hypothesis
  gasThroughputOpportunity
  "Gas hot-water and cooking appliances create opportunities for throughput-linked gas consumption. Actual consumption, revenue and beneficiary magnitude are unmeasured."
  false
  "Metered gas consumption, tariff components and asset-owner revenue allocation."

hotWaterWasteDemandResidual : DemandHypothesis
hotWaterWasteDemandResidual = demand-hypothesis
  hotWaterDrawBeforeUsefulTemperature
  "The observed delay before useful hot water reaches the kitchen can cause water to be discharged while the instantaneous unit is operating. The quantity of water, gas and energy attributable to this delay is not yet measured."
  false
  "Timed flow-rate measurement, pipe-route/dead-leg volume, unit input rate, outlet-temperature trace and gas-meter interval data."

wokBurnerInducedDemandResidual : DemandHypothesis
wokBurnerInducedDemandResidual = demand-hypothesis
  highHeatGasCookingCapability
  "Installing a gas wok burner provides a dedicated gas-use capability in a dwelling that otherwise has electrical cooking capacity. Whether that feature was selected to induce gas connection/use, satisfy buyer preference or for another design reason remains unpaid."
  false
  "Azure sales/inclusions specification, design brief, appliance procurement record, purchaser options schedule and project gas-reticulation rationale."

networkUtilisationResidual : DemandHypothesis
networkUtilisationResidual = demand-hypothesis
  networkAssetUtilisation
  "Additional connected dwellings may improve utilisation of an existing reticulated-gas network, but the economic effect on the relevant Springfield gas assets has not been quantified."
  false
  "Original Springfield gas-network business case, connection forecasts/actuals, asset register, access-arrangement revenue model and current ownership chain."

------------------------------------------------------------------------
-- Source anchors for the economic proposition only.
------------------------------------------------------------------------

allgasReferenceTariffStructure : Source.AttributedSource
allgasReferenceTariffStructure = Source.mkNoDOISource
  "Australian Energy Regulator / APT Allgas"
  "Allgas Access Arrangement Information — pricing structures"
  "Regulated gas access-arrangement material"
  "2010-2011"
  "https://www.aemc.gov.au/media/62065"
  Source.governmentSource
  "Regulatory source stating that Allgas reference-tariff design includes daily fixed charges and throughput charges, and that fixed charges recover portions of service, metering and administration costs. This supports the existence of fixed and throughput revenue mechanisms in the network tariff structure; it does not identify the tariff or revenue attributable to the observed endpoint."
  Source.publicAttribution

allgasCurrentOwnership : Source.AttributedSource
allgasCurrentOwnership = Source.mkNoDOISource
  "Australian Energy Market Commission"
  "QLD: Allgas gas distribution network"
  "Gas pipeline register"
  "2026"
  "https://www.aemc.gov.au/energy-system/gas/gas-pipeline-register/qld-allgas-gas-distribution-network"
  Source.governmentSource
  "Current register source stating that Allgas Energy is owned by Stonepeak and operated by AGIG after the March 2026 acquisition. This pays current network-level ownership, not same-object ownership of the exact Springfield service line or revenue from the observed endpoint."
  Source.publicAttribution

------------------------------------------------------------------------
-- Net-zero tension is an accounting residual, not a greenwashing conclusion.
------------------------------------------------------------------------

data NetZeroQuestion : Set where
  operationalGasInsideBoundary : NetZeroQuestion
  legacyGasTreatment : NetZeroQuestion
  newGasConnectionCompatibility : NetZeroQuestion
  rooftopSolarGasInteraction : NetZeroQuestion

record NetZeroResidual : Set where
  constructor net-zero-residual
  field
    question : NetZeroQuestion
    missingObject : String
    paid : Bool

open NetZeroResidual public

azureGasWithinSpringfieldNetZeroBoundaryResidual : NetZeroResidual
azureGasWithinSpringfieldNetZeroBoundaryResidual = net-zero-residual
  operationalGasInsideBoundary
  "Greater Springfield net-zero accounting boundary/methodology plus Azure project operational-energy specification showing whether reticulated fossil gas consumption is included, excluded, offset or scheduled for phase-out."
  false

newGasConnectionCompatibilityResidual : NetZeroResidual
newGasConnectionCompatibilityResidual = net-zero-residual
  newGasConnectionCompatibility
  "Project-specific evidence showing whether the Azure dwelling is a new gas connection, inherited connection, purchaser option or mandatory specification, and how that choice was reconciled with the Greater Springfield net-zero/electrification program."
  false

------------------------------------------------------------------------
-- Corruption / lobbying promotion gates.
------------------------------------------------------------------------

data AzureGasCorruptionPaid : Set where
data AzureGasLobbyingCausationPaid : Set where
data WastefulDemandProvesIntent : Set where
data NetZeroLabelProvesNoFossilGas : Set where
data AzureDeveloperIdentityProvesGasLobbying : Set where
data FixedChargeBenefitProvesDeveloperKickback : Set where

azureGasCorruptionRemainsUnpaid : AzureGasCorruptionPaid → ⊥
azureGasCorruptionRemainsUnpaid ()

azureGasLobbyingCausationRemainsUnpaid : AzureGasLobbyingCausationPaid → ⊥
azureGasLobbyingCausationRemainsUnpaid ()

wastefulDemandDoesNotProveIntent : WastefulDemandProvesIntent → ⊥
wastefulDemandDoesNotProveIntent ()

netZeroLabelDoesNotProveNoFossilGas : NetZeroLabelProvesNoFossilGas → ⊥
netZeroLabelDoesNotProveNoFossilGas ()

azureDeveloperIdentityDoesNotProveGasLobbying : AzureDeveloperIdentityProvesGasLobbying → ⊥
azureDeveloperIdentityDoesNotProveGasLobbying ()

fixedChargeBenefitDoesNotProveDeveloperKickback : FixedChargeBenefitProvesDeveloperKickback → ⊥
fixedChargeBenefitDoesNotProveDeveloperKickback ()

------------------------------------------------------------------------
-- Highest-alpha ordered payments.
------------------------------------------------------------------------

data InducedDemandParetoLeaf : Set where
  exactAzureProjectIdentity : InducedDemandParetoLeaf
  exactAzureInclusionsAndHydraulics : InducedDemandParetoLeaf
  exactGasConnectionAndTariff : InducedDemandParetoLeaf
  exactHotWaterDeadLegMeasurement : InducedDemandParetoLeaf
  exactNetZeroAccountingBoundary : InducedDemandParetoLeaf
  exactSpringfieldGasBusinessCase : InducedDemandParetoLeaf
  exactLobbyingSubjectMatter : InducedDemandParetoLeaf
  exactCommercialBenefitOrConsideration : InducedDemandParetoLeaf

record InducedDemandParetoPolicy : Set where
  constructor induced-demand-pareto-policy
  field
    developerIdentityBeforeAttribution : Bool
    projectSpecificationBeforeDesignIntent : Bool
    measurementBeforeWasteMagnitude : Bool
    tariffBeforeRevenueMagnitude : Bool
    netZeroBoundaryBeforeInconsistencyClaim : Bool
    lobbyingSubjectBeforeInfluenceClaim : Bool
    considerationBeforeCorruptionClaim : Bool
    secondaryMayLocatePrimary : Bool
    secondaryMayPayPrimary : Bool

canonicalInducedDemandPareto : InducedDemandParetoPolicy
canonicalInducedDemandPareto = induced-demand-pareto-policy
  true true true true true true true true false
