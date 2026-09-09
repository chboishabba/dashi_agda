module DASHI.Environment.BerkeleyRapidThermophilicCompostingExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Environment.SustainableAgricultureManagementSourceRegistryExact as Sources
import DASHI.Environment.SoilBiogeochemistryProcessNetworkExact as Soil

------------------------------------------------------------------------
-- BERKELEY / RAABE RAPID COMPOSTING: SOURCE-BOUND PROCESS SURFACE
--
-- Historical source calibration:
--   Robert D. Raabe, Professor of Plant Pathology, University of California,
--   Berkeley, "The Rapid Composting Method", UC Vegetable Research and
--   Information Center / UC ANR archival publication.
--   Canonical recovery: UC ANR rapidcompost.pdf.
--
-- Current evidence calibration:
--   Journal of Environmental Management 354 (2024) 120337,
--   DOI 10.1016/j.jenvman.2024.120337, review of GHG emissions and process
--   factors in agricultural-waste composting.
--   Global livestock-manure compost meta-analysis (2023), PMID 37146823.
--
-- SOURCE BOUNDARY
-- Raabe supports the rapid-turning / feedstock-preparation process lineage.
-- The typed state machine, evidence separation, soil weld and no-promotion
-- theorems are DASHI reconstruction. Modern reviews calibrate process-factor
-- dependence; they do not certify every Berkeley-method pile.
------------------------------------------------------------------------

data CompostPhase : Set where
  assembled mesophilic thermophilic cooling curing finishedCandidate : CompostPhase

data AerationMode : Set where
  passiveAeration manualTurning forcedAeration : AerationMode

data CompostOutcome : Set where
  temperatureTrajectory
  oxygenStatus
  moistureStatus
  massReduction
  organicMatterStability
  maturity
  pathogenReduction
  ammoniaLoss
  methaneEmission
  nitrousOxideEmission
  carbonRetention
  nitrogenRetention
  soilAmendmentResponse : CompostOutcome

data EvidenceStatus : Set where
  protocolDescribed processObserved labMeasured fieldMeasured causalEstimate replicated : EvidenceStatus

record RapidCompostProtocol : Set where
  constructor rapid-compost-protocol
  field
    sourceStage : Sources.ClaimStage
    feedstockReference : String
    particleSizeReference : String
    nominalCarbonNitrogenReference : String
    moistureReference : String
    pileGeometryReference : String
    aerationMode : AerationMode
    turningScheduleReference : String
    temperatureMonitoringReference : String
    targetDurationReference : String

open RapidCompostProtocol public

berkeleyRaabeProtocol : RapidCompostProtocol
berkeleyRaabeProtocol = rapid-compost-protocol
  Sources.externalSourceClaim
  "mixed organic compostable feedstocks; exact mixture remains implementation-specific"
  "Raabe rapid-compost source emphasizes size reduction, especially for woody material"
  "initial mixture balance is an operational coordinate, not a universal bioavailable C:N theorem"
  "moist enough for aerobic decomposition without defining one universal percentage"
  "pile geometry must support self-heating and oxygen exchange"
  manualTurning
  "frequent turning is part of the rapid-process lineage; actual schedule is protocol/context specific"
  "pile temperature trajectory should be observed rather than inferred from elapsed days"
  "rapid timetable is a process target, not a maturity certificate"

record CompostBatch : Set where
  constructor compost-batch
  field
    protocol : RapidCompostProtocol
    phase : CompostPhase
    batchId : String
    feedstockLot : String
    siteContext : String
    startTimeReference : String
    oxygenMeasurementReference : String
    moistureMeasurementReference : String
    temperatureTrajectoryReference : String

open CompostBatch public

record CompostOutcomeEvidence : Set where
  constructor compost-outcome-evidence
  field
    batch : CompostBatch
    outcome : CompostOutcome
    evidenceStatus : EvidenceStatus
    measurementMethod : String
    comparator : String
    resultReference : String
    uncertaintyReference : String

open CompostOutcomeEvidence public

------------------------------------------------------------------------
-- Thermophilic exposure, sanitation, stability and maturity are distinct.
------------------------------------------------------------------------

record ThermophilicExposureReceipt (batch : CompostBatch) : Set where
  constructor thermophilic-exposure-receipt
  field
    temperatureReference : String
    timeAtTemperatureReference : String
    spatialCoverageReference : String

open ThermophilicExposureReceipt public

record PathogenReductionReceipt (batch : CompostBatch) : Set where
  constructor pathogen-reduction-receipt
  field
    thermophilicExposure : ThermophilicExposureReceipt batch
    targetOrganismOrIndicator : String
    criterionOrStandardReference : String
    samplingReference : String
    resultReference : String

open PathogenReductionReceipt public

record MaturityReceipt (batch : CompostBatch) : Set where
  constructor maturity-receipt
  field
    stabilityMethodReference : String
    maturityMethodReference : String
    curingReference : String
    resultReference : String

open MaturityReceipt public

------------------------------------------------------------------------
-- Same-object weld into the existing soil C/N process network.
------------------------------------------------------------------------

record CompostToSoilCNAdapter (soil : Soil.SoilCNProcessNetwork) : Set₁ where
  constructor compost-to-soil-cn-adapter
  field
    finishedBatch : CompostBatch
    maturityEvidence : MaturityReceipt finishedBatch
    amendmentApplicationReference : String
    soilNetwork : Soil.SoilCNProcessNetwork
    sameSoilNetwork : soilNetwork ≡ soil
    carbonPoolMappingReference : String
    nitrogenPoolMappingReference : String
    decompositionProcessMappingReference : String
    conservationReference : String
    fieldOutcomeEvidenceReference : String

open CompostToSoilCNAdapter public

------------------------------------------------------------------------
-- Attribution / causal firewalls.
------------------------------------------------------------------------

data HotMeansMaturePermission : Set where
data ThermophilicMeansSterilePermission : Set where
data ElapsedDaysMeansMaturePermission : Set where
data RapidCompostMeansCarbonSequestrationPermission : Set where
data MoreTurningMeansLowerEmissionsPermission : Set where
data NominalCNMeansBioavailableCNPermission : Set where
data CompostApplicationMeansSoilBenefitPermission : Set where

hotDoesNotProveMaturity : HotMeansMaturePermission → ⊥
hotDoesNotProveMaturity ()

thermophilicDoesNotMeanSterile : ThermophilicMeansSterilePermission → ⊥
thermophilicDoesNotMeanSterile ()

elapsedDaysDoNotProveMaturity : ElapsedDaysMeansMaturePermission → ⊥
elapsedDaysDoNotProveMaturity ()

rapidCompostDoesNotProveCarbonSequestration : RapidCompostMeansCarbonSequestrationPermission → ⊥
rapidCompostDoesNotProveCarbonSequestration ()

moreTurningDoesNotUniversallyLowerEmissions : MoreTurningMeansLowerEmissionsPermission → ⊥
moreTurningDoesNotUniversallyLowerEmissions ()

nominalCNDoesNotEqualBioavailableCN : NominalCNMeansBioavailableCNPermission → ⊥
nominalCNDoesNotEqualBioavailableCN ()

compostApplicationDoesNotProveSoilBenefit : CompostApplicationMeansSoilBenefitPermission → ⊥
compostApplicationDoesNotProveSoilBenefit ()

record BerkeleyRapidCompostBoundary : Set where
  constructor berkeley-rapid-compost-boundary
  field
    historicalProtocolAndModernOutcomeEvidenceDistinct : Bool
    thermophilicExposureAndMaturityDistinct : Bool
    pathogenReductionNeedsTargetAndCriterion : Bool
    emissionsNeedMeasurementOrModelReceipt : Bool
    soilBenefitNeedsFieldEvidence : Bool
    rapidScheduleAutomaticallyCertifiesMaturity : Bool

canonicalBerkeleyRapidCompostBoundary : BerkeleyRapidCompostBoundary
canonicalBerkeleyRapidCompostBoundary =
  berkeley-rapid-compost-boundary true true true true true false
