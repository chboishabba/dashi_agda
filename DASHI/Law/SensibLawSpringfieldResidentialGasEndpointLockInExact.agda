module DASHI.Law.SensibLawSpringfieldResidentialGasEndpointLockInExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Law.SensibLawSpringfieldGasLobbyingOwnershipSnowballExact as Influence

------------------------------------------------------------------------
-- DEMAND-SIDE GAS ENDPOINT / LOCK-IN INVESTIGATIVE OWNER
--
-- This owner keeps three layers separate:
--   (1) de-identified investigator observations at a residential endpoint;
--   (2) documented Springfield gas-network / developer / lobbyist relationships;
--   (3) hypotheses about demand creation, fossil-industry benefit or lobbying.
--
-- Household observations generate acquisition targets. They do not by themselves
-- prove code breach, unsafe installation, developer intent, ownership, lobbying
-- causation or a fossil-fuel beneficiary relationship.
------------------------------------------------------------------------

data EndpointFeature : Set where
  instantaneousGasHotWater : EndpointFeature
  mixedGasElectricCooking : EndpointFeature
  rooftopSolar : EndpointFeature
  delayedHotWaterAtKitchen : EndpointFeature
  repeatedIgnitionBurstObservation : EndpointFeature
  combustionLikeOdourNearOutdoorUnit : EndpointFeature
  recurrentAlarmSoundInComplex : EndpointFeature

data ObservationStatus : Set where
  operatorReported : ObservationStatus
  instrumentVerified : ObservationStatus
  sourceDocumentPaid : ObservationStatus
  unresolved : ObservationStatus

record EndpointObservation : Set where
  constructor endpoint-observation
  field
    feature : EndpointFeature
    statement : String
    status : ObservationStatus
    exactAddressPublished : Bool
    exactAddressPublishedIsFalse : exactAddressPublished ≡ false

open EndpointObservation public

springfieldEndpointGasHotWater : EndpointObservation
springfieldEndpointGasHotWater = endpoint-observation
  instantaneousGasHotWater
  "De-identified investigator observation: the residential endpoint uses instantaneous gas hot water."
  operatorReported
  false refl

springfieldEndpointMixedCooking : EndpointObservation
springfieldEndpointMixedCooking = endpoint-observation
  mixedGasElectricCooking
  "De-identified investigator observation: the cooking configuration is mixed gas/electric rather than all-electric."
  operatorReported
  false refl

springfieldEndpointSolar : EndpointObservation
springfieldEndpointSolar = endpoint-observation
  rooftopSolar
  "De-identified investigator observation: the dwelling also has rooftop solar, so gas demand coexists with distributed electricity generation."
  operatorReported
  false refl

springfieldEndpointHotWaterDelay : EndpointObservation
springfieldEndpointHotWaterDelay = endpoint-observation
  delayedHotWaterAtKitchen
  "De-identified investigator observation: hot water at the kitchen tap may require roughly a minute of running before useful hot water arrives."
  operatorReported
  false refl

springfieldEndpointIgnitionBurst : EndpointObservation
springfieldEndpointIgnitionBurst = endpoint-observation
  repeatedIgnitionBurstObservation
  "De-identified investigator observation: short off/on hot-water cycles can produce a noticeable ignition/start-up gas event. No gas-flow measurement is yet attached."
  operatorReported
  false refl

springfieldEndpointOutdoorOdour : EndpointObservation
springfieldEndpointOutdoorOdour = endpoint-observation
  combustionLikeOdourNearOutdoorUnit
  "De-identified investigator observation: the outdoor patio area near the hot-water unit can have an exhaust-like odour. Odour is not treated as a methane or carbon-monoxide measurement."
  operatorReported
  false refl

springfieldEndpointAlarmObservation : EndpointObservation
springfieldEndpointAlarmObservation = endpoint-observation
  recurrentAlarmSoundInComplex
  "De-identified investigator observation: alarm sounds are heard periodically in the residential complex. Cause is unknown and no gas-event attribution is made."
  operatorReported
  false refl

------------------------------------------------------------------------
-- Public sources that locate the supply-side / lobbying search.
------------------------------------------------------------------------

springfieldGasAllianceSecondary : Source.AttributedSource
springfieldGasAllianceSecondary = Influence.springfieldGasAllianceReport

allgasStreetRegister : Source.AttributedSource
allgasStreetRegister = Source.mkNoDOISource
  "Allgas"
  "Gas in My Street — March 2026"
  "Allgas street register"
  "2026"
  "https://allgas.com.au/wp-content/uploads/2026/03/Gas_In_My_Street_-_Allgas_March_2026.pdf"
  Source.practitionerSource
  "Current network-service locator listing multiple Greater Springfield streets as having natural-gas service. It does not establish which developer selected gas appliances for a particular dwelling."
  Source.publicAttribution

santoroFossilRTILocator : Source.AttributedSource
santoroFossilRTILocator = Source.mkNoDOISource
  "Queensland Government"
  "Former Department of Energy and Water Supply disclosure log — 2013, application 12-370 Min"
  "Right to Information disclosure log"
  "2013"
  "https://www.nrmmrrd.qld.gov.au/legal/right-to-information/disclosure-log/disclosure-log-former-department-of-energy-and-water-supply"
  Source.governmentSource
  "Primary RTI-log locator: a request for documents concerning Santo Santoro or Santoro Consulting expressly excluded documents to/from Waratah Coal, Fairway Coal, Styx Coal, Mineralogy, Queensland Nickel and Clive Palmer. This pays a historical documentary adjacency/search coordinate, not that every named entity was a Santoro client and not that Springfield lobbying concerned fossil-fuel matters."
  Source.publicAttribution

springfieldLobbying2025 : Source.AttributedSource
springfieldLobbying2025 = Influence.springfieldLobbyingDiary

springfieldLobbying2025April : Source.AttributedSource
springfieldLobbying2025April = Source.mkNoDOISource
  "Queensland Government"
  "Chief of Staff diary — April 2025"
  "Department of the Premier and Cabinet"
  "2025"
  "https://www.premiers.qld.gov.au/right-to-info/published-info/assets/chief-of-staff-diaries-2025-04.pdf"
  Source.governmentSource
  "Primary diary locator recording a 16 April 2025 meeting with Santo Santoro, Santoro Consulting, Springfield Land Corporation identified with the lobbyist marker, and Springfield City Group representatives. Meeting purpose was Springfield City Group; no fossil-fuel subject is imported."
  Source.publicAttribution

springfieldLobbying2025July : Source.AttributedSource
springfieldLobbying2025July = Source.mkNoDOISource
  "Queensland Government"
  "Ministerial diary — Minister for Finance, Trade, Employment and Training — July 2025"
  "Queensland Cabinet"
  "2025"
  "https://cabinet.qld.gov.au/ministers-portfolios/assets/diary/current/rosslyn-bates/2025/july/rosslyn-bates.pdf"
  Source.governmentSource
  "Primary diary locator recording a 10 July 2025 meeting with Santo Santoro identified as registered lobbyist, described as an update on Springfield City Group Plan. No gas or fossil-fuel topic is imported."
  Source.publicAttribution

------------------------------------------------------------------------
-- Hypothesis fibres and required primary payments.
------------------------------------------------------------------------

data GasLockInHypothesis : Set where
  developerSpecifiedGasEndpoints : GasLockInHypothesis
  gasNetworkConnectionWasCommercialDesignObjective : GasLockInHypothesis
  gasInfrastructureOwnerBenefitsFromResidentialLoad : GasLockInHypothesis
  springfieldLobbyingIncludedGasOrFossilPolicy : GasLockInHypothesis
  azureSpringfieldPartnershipCarriedGasSpecification : GasLockInHypothesis
  fossilLobbyNetworkInfluencedResidentialDesign : GasLockInHypothesis

data RequiredProducer : Set where
  originalEnergexSpringfieldAlliance : RequiredProducer
  subdivisionGasReticulationPlans : RequiredProducer
  projectHydraulicAndGasPlans : RequiredProducer
  applianceSchedulesAndMarketingSpecifications : RequiredProducer
  gasMeterNMIorMIRNAndDistributorIdentity : RequiredProducer
  builderDeveloperSupplyContracts : RequiredProducer
  allgasHistoricalAssetRegisterAndEasements : RequiredProducer
  santoroClientRegisterAtMeetingDates : RequiredProducer
  meetingBriefsCorrespondenceAndOutcomeRecords : RequiredProducer
  azureSpringfieldProjectSPVAndSpecificationChain : RequiredProducer
  instrumentedGasFlowAndCombustionMeasurements : RequiredProducer

record HypothesisPayment : Set where
  constructor hypothesis-payment
  field
    hypothesis : GasLockInHypothesis
    producer : RequiredProducer
    paid : Bool
    paymentBoundary : String

open HypothesisPayment public

developerSpecifiedGasEndpointsResidual : HypothesisPayment
developerSpecifiedGasEndpointsResidual = hypothesis-payment
  developerSpecifiedGasEndpoints
  applianceSchedulesAndMarketingSpecifications
  false
  "Observed gas appliances do not identify who specified them. Acquire original sales/build specification, appliance schedule, hydraulic/gas plan and any variation record for the exact dwelling/project."

gasNetworkCommercialObjectiveResidual : HypothesisPayment
gasNetworkCommercialObjectiveResidual = hypothesis-payment
  gasNetworkConnectionWasCommercialDesignObjective
  originalEnergexSpringfieldAlliance
  false
  "The 2004 ABC report locates an Energex–Springfield alliance and an Energex statement about 8,000 gas connections, but the original agreement/business case remains unpaid."

gasOwnerBenefitResidual : HypothesisPayment
gasOwnerBenefitResidual = hypothesis-payment
  gasInfrastructureOwnerBenefitsFromResidentialLoad
  allgasHistoricalAssetRegisterAndEasements
  false
  "Current natural-gas service in Greater Springfield plus historical Energex/Allgas chronology does not yet weld the exact Springfield asset into the sale/ownership chain or quantify revenue/load benefit."

springfieldFossilLobbyResidual : HypothesisPayment
springfieldFossilLobbyResidual = hypothesis-payment
  springfieldLobbyingIncludedGasOrFossilPolicy
  meetingBriefsCorrespondenceAndOutcomeRecords
  false
  "Springfield used a registered lobbyist and the same lobbying firm appears in historical RTI search coordinates involving coal/mineral entities, but subject-matter identity is unpaid. Acquire client register, meeting briefs, correspondence and downstream decisions for the Springfield meetings."

azureGasSpecificationResidual : HypothesisPayment
azureGasSpecificationResidual = hypothesis-payment
  azureSpringfieldPartnershipCarriedGasSpecification
  azureSpringfieldProjectSPVAndSpecificationChain
  false
  "Repeated Azure–Springfield project partnership does not show that Azure or Springfield specified gas at the observed endpoint. Acquire project-specific SPV, title, building approval, appliance/hydraulic schedule and handover documentation."

combustionMeasurementResidual : HypothesisPayment
combustionMeasurementResidual = hypothesis-payment
  gasInfrastructureOwnerBenefitsFromResidentialLoad
  instrumentedGasFlowAndCombustionMeasurements
  false
  "Odour, ignition noise and hot-water delay are observations only. Gas flow, combustion products, carbon monoxide and appliance safety require instrumented/licensed assessment."

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data GasApplianceProvesDeveloperIntent : Set where
data HotWaterDelayProvesWasteDesignIntent : Set where
data OdourProvesGasLeak : Set where
data AlarmSoundProvesGasIncident : Set where
data SharedLobbyistProvesFossilCoordination : Set where
data FossilClientAdjacencyProvesSpringfieldFossilLobbying : Set where
data NetworkServiceProvesDeveloperOwnership : Set where
data SolarPlusGasProvesGreenwashing : Set where

gasApplianceDoesNotProveDeveloperIntent : GasApplianceProvesDeveloperIntent → ⊥
gasApplianceDoesNotProveDeveloperIntent ()

hotWaterDelayDoesNotProveWasteDesignIntent : HotWaterDelayProvesWasteDesignIntent → ⊥
hotWaterDelayDoesNotProveWasteDesignIntent ()

odourDoesNotProveGasLeak : OdourProvesGasLeak → ⊥
odourDoesNotProveGasLeak ()

alarmDoesNotProveGasIncident : AlarmSoundProvesGasIncident → ⊥
alarmDoesNotProveGasIncident ()

sharedLobbyistDoesNotProveFossilCoordination : SharedLobbyistProvesFossilCoordination → ⊥
sharedLobbyistDoesNotProveFossilCoordination ()

fossilAdjacencyDoesNotProveSpringfieldFossilLobbying : FossilClientAdjacencyProvesSpringfieldFossilLobbying → ⊥
fossilAdjacencyDoesNotProveSpringfieldFossilLobbying ()

networkServiceDoesNotProveDeveloperOwnership : NetworkServiceProvesDeveloperOwnership → ⊥
networkServiceDoesNotProveDeveloperOwnership ()

solarPlusGasDoesNotProveGreenwashing : SolarPlusGasProvesGreenwashing → ⊥
solarPlusGasDoesNotProveGreenwashing ()

------------------------------------------------------------------------
-- Pareto: pay the shortest chain from household endpoint to upstream actor.
------------------------------------------------------------------------

record EndpointToUpstreamPareto : Set where
  constructor endpoint-to-upstream-pareto
  field
    exactDwellingSpecificationFirst : Bool
    exactDistributorIdentitySecond : Bool
    exactDeveloperProjectSPVThird : Bool
    exactGasAllianceAssetChainFourth : Bool
    lobbyingSubjectMatterAfterIdentity : Bool
    beneficiaryClaimOnlyAfterRevenueOrContractReceipt : Bool
    householdObservationMaySelectProducer : Bool
    householdObservationMayPromoteCausation : Bool

canonicalEndpointToUpstreamPareto : EndpointToUpstreamPareto
canonicalEndpointToUpstreamPareto = endpoint-to-upstream-pareto
  true true true true true true true false
