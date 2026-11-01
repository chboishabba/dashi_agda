module DASHI.Education.DigitalESDMaterialEnvironmentalSubstrateExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attr
import DASHI.Education.DigitalESDAcquisitionSnowballParetoExact as Sources
import DASHI.Education.DigitalESDSourceAttributionCorrectionExact as Correction
import DASHI.Education.DigitalESDExternalityIncidenceAuditExact as Incidence
import DASHI.Economics.TSMCHBMManufacturingDemandPolicy2026Exact as TSMC
import DASHI.Environment.LESResearchCrossPollinationExact as LES

------------------------------------------------------------------------
-- MATERIAL / ENVIRONMENTAL SUBSTRATE AUDIT
--
-- "Digital", "AI", "online" and "cloud" are service labels, not dematerialised
-- systems.  The educational consumer must retain the lifecycle coordinates it
-- actually needs: chips, devices, networks/data centres, electricity, water,
-- materials, repair/service life, e-waste and the people/places carrying those
-- burdens.  Generic infrastructure evidence never becomes the footprint of a
-- named school/university deployment without same-object measurement/model data.
------------------------------------------------------------------------

tsmc2025SustainabilitySource : Attr.AttributedSource
tsmc2025SustainabilitySource =
  Attr.mkNoDOISource
    "Taiwan Semiconductor Manufacturing Company Limited"
    "2025 Sustainability Report"
    "TSMC"
    "2026"
    "https://www.tsmc.com/english/aboutTSMC/dc_csr_report"
    Attr.institutionalSource
    "Primary company sustainability-report surface for semiconductor manufacturing energy, water, materials and waste context. Company-reported metrics are retained with source role and do not create a digital-education deployment footprint or an independent environmental audit."
    Attr.publicAttribution

ieaEnergyAISubstrateSource : Attr.AttributedSource
ieaEnergyAISubstrateSource =
  Attr.mkNoDOISource
    "International Energy Agency"
    "Energy and AI"
    "IEA"
    "2025"
    "https://www.iea.org/reports/energy-and-ai"
    Attr.institutionalSource
    "Global/regional energy-system modelling for AI/data-centre electricity demand, supply, emissions, security and uncertainty. General infrastructure context only; does not identify energy use of a named educational AI task or deployment."
    Attr.publicAttribution

materialContextSources : List Attr.AttributedSource
materialContextSources =
  Sources.ieaEnergyAISource
  ∷ Sources.ituGlobalEwasteSource
  ∷ Correction.pinzoneEducationLCACorrectedSource
  ∷ tsmc2025SustainabilitySource
  ∷ ieaEnergyAISubstrateSource
  ∷ []

data DigitalMaterialStage : Set where
  semiconductorFabrication : DigitalMaterialStage
  deviceManufacture : DigitalMaterialStage
  procurementDistribution : DigitalMaterialStage
  networkAndDataCentre : DigitalMaterialStage
  operationalEnergyWater : DigitalMaterialStage
  maintenanceRepairUpgrade : DigitalMaterialStage
  replacementEndOfLife : DigitalMaterialStage
  recoveryRecyclingDisposal : DigitalMaterialStage

digitalMaterialStages : List DigitalMaterialStage
digitalMaterialStages =
  semiconductorFabrication
  ∷ deviceManufacture
  ∷ procurementDistribution
  ∷ networkAndDataCentre
  ∷ operationalEnergyWater
  ∷ maintenanceRepairUpgrade
  ∷ replacementEndOfLife
  ∷ recoveryRecyclingDisposal
  ∷ []

digitalMaterialStageCount : Nat
digitalMaterialStageCount = 8

data MaterialAuditQuestion : Set where
  whichDevicesAndAccelerators : MaterialAuditQuestion
  whereComputeOccurs : MaterialAuditQuestion
  whichElectricityAndGridContext : MaterialAuditQuestion
  whichWaterAndCoolingContext : MaterialAuditQuestion
  whichEmbodiedMaterialsAndFabrication : MaterialAuditQuestion
  whatServiceLifeReplacementCycle : MaterialAuditQuestion
  whatRepairUpgradeReuseOptions : MaterialAuditQuestion
  whatEndOfLifeAndEwasteRoute : MaterialAuditQuestion
  whichCommunitiesWorkersBearBurden : MaterialAuditQuestion
  whichEnvironmentalQuantityActuallyMeasured : MaterialAuditQuestion

materialAuditQuestions : List MaterialAuditQuestion
materialAuditQuestions =
  whichDevicesAndAccelerators
  ∷ whereComputeOccurs
  ∷ whichElectricityAndGridContext
  ∷ whichWaterAndCoolingContext
  ∷ whichEmbodiedMaterialsAndFabrication
  ∷ whatServiceLifeReplacementCycle
  ∷ whatRepairUpgradeReuseOptions
  ∷ whatEndOfLifeAndEwasteRoute
  ∷ whichCommunitiesWorkersBearBurden
  ∷ whichEnvironmentalQuantityActuallyMeasured
  ∷ []

materialAuditQuestionCount : Nat
materialAuditQuestionCount = 10

questionReading : MaterialAuditQuestion → String
questionReading whichDevicesAndAccelerators = "which learner/staff devices, servers, GPUs/accelerators and networking equipment are required?"
questionReading whereComputeOccurs = "which computation occurs locally, institutionally, in colocation/hyperscale data centres or across several carriers?"
questionReading whichElectricityAndGridContext = "what electricity demand and physical grid/fuel context belongs to the measured/modelled system boundary?"
questionReading whichWaterAndCoolingContext = "what direct/indirect water and cooling assumptions or measurements belong to the same system boundary?"
questionReading whichEmbodiedMaterialsAndFabrication = "which semiconductor/device fabrication, raw-material and embodied-impact stages are included or omitted?"
questionReading whatServiceLifeReplacementCycle = "what device/server service life, refresh and replacement assumptions drive lifecycle burden?"
questionReading whatRepairUpgradeReuseOptions = "which repair, upgrade, reuse, portability and maintenance options are practically available?"
questionReading whatEndOfLifeAndEwasteRoute = "what collection, reuse, recycling, export, landfill or other end-of-life route is actually evidenced?"
questionReading whichCommunitiesWorkersBearBurden = "which manufacturing, energy, water, waste, institutional and household communities/workers bear lifecycle burdens?"
questionReading whichEnvironmentalQuantityActuallyMeasured = "is the claimed quantity measured, inventory-derived, modelled, scenario-projected or merely contextual?"

------------------------------------------------------------------------
-- Canonical donor boundaries retained without domain promotion.
------------------------------------------------------------------------

externalityBoundary : Incidence.ExternalityIncidenceBoundary
externalityBoundary = Incidence.canonicalExternalityIncidenceBoundary

tsmcCalibration : TSMC.ManufacturingDemandPolicyCalibration
tsmcCalibration = TSMC.canonicalManufacturingDemandPolicyCalibration

lesTaskRelativeReading : String
lesTaskRelativeReading =
  "LES TaskFactorisation is retained as the generic consumer-relative sufficiency donor: an environmental projection is adequate only for the declared task/output it actually factorises, not for every sustainability consumer."

------------------------------------------------------------------------
-- No-promotion firewalls.
------------------------------------------------------------------------

data AILabelCreatesDeploymentFootprint : Set where
data DeviceCountCreatesEnvironmentalSustainability : Set where
data GlobalDataCentreAverageCreatesSchoolAIUsage : Set where
data TSMCReportCreatesEducationLifecycleMeasurement : Set where
data RecycledFractionCreatesCircularity : Set where
data RenewableProcurementCreatesZeroImpact : Set where
data EwasteCollectionCreatesMaterialRecovery : Set where
data ModelledImpactCreatesMeasuredImpact : Set where

data InfrastructureEfficiencyCreatesAbsoluteBurdenReduction : Set where

aiLabelDoesNotCreateDeploymentFootprint : AILabelCreatesDeploymentFootprint → ⊥
aiLabelDoesNotCreateDeploymentFootprint ()

deviceCountDoesNotCreateEnvironmentalSustainability : DeviceCountCreatesEnvironmentalSustainability → ⊥
deviceCountDoesNotCreateEnvironmentalSustainability ()

globalDataCentreAverageDoesNotCreateSchoolAIUsage : GlobalDataCentreAverageCreatesSchoolAIUsage → ⊥
globalDataCentreAverageDoesNotCreateSchoolAIUsage ()

tsmcReportDoesNotCreateEducationLifecycleMeasurement : TSMCReportCreatesEducationLifecycleMeasurement → ⊥
tsmcReportDoesNotCreateEducationLifecycleMeasurement ()

recycledFractionDoesNotCreateCircularity : RecycledFractionCreatesCircularity → ⊥
recycledFractionDoesNotCreateCircularity ()

renewableProcurementDoesNotCreateZeroImpact : RenewableProcurementCreatesZeroImpact → ⊥
renewableProcurementDoesNotCreateZeroImpact ()

ewasteCollectionDoesNotCreateMaterialRecovery : EwasteCollectionCreatesMaterialRecovery → ⊥
ewasteCollectionDoesNotCreateMaterialRecovery ()

modelledImpactDoesNotCreateMeasuredImpact : ModelledImpactCreatesMeasuredImpact → ⊥
modelledImpactDoesNotCreateMeasuredImpact ()

infrastructureEfficiencyDoesNotCreateAbsoluteBurdenReduction :
  InfrastructureEfficiencyCreatesAbsoluteBurdenReduction → ⊥
infrastructureEfficiencyDoesNotCreateAbsoluteBurdenReduction ()

record MaterialEnvironmentalBoundary : Set where
  constructor material-environmental-boundary
  field
    digitalServiceRetainsPhysicalSubstrate : Bool
    digitalServiceRetainsPhysicalSubstrateIsTrue : digitalServiceRetainsPhysicalSubstrate ≡ true
    semiconductorManufacturingRetained : Bool
    semiconductorManufacturingRetainedIsTrue : semiconductorManufacturingRetained ≡ true
    energyWaterMaterialLifecycleRetained : Bool
    energyWaterMaterialLifecycleRetainedIsTrue : energyWaterMaterialLifecycleRetained ≡ true
    repairReplacementEwasteRetained : Bool
    repairReplacementEwasteRetainedIsTrue : repairReplacementEwasteRetained ≡ true
    burdenIncidenceRetained : Bool
    burdenIncidenceRetainedIsTrue : burdenIncidenceRetained ≡ true
    generalInfrastructureContextEqualsDeploymentFootprint : Bool
    generalInfrastructureContextEqualsDeploymentFootprintIsFalse : generalInfrastructureContextEqualsDeploymentFootprint ≡ false
    modelledEqualsMeasured : Bool
    modelledEqualsMeasuredIsFalse : modelledEqualsMeasured ≡ false

open MaterialEnvironmentalBoundary public

canonicalMaterialEnvironmentalBoundary : MaterialEnvironmentalBoundary
canonicalMaterialEnvironmentalBoundary =
  material-environmental-boundary
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl

materialEnvironmentalReading : String
materialEnvironmentalReading =
  "Digital education is physically substrate-bound. AI and ordinary computing consume chips, devices, networking/data-centre infrastructure, electricity, water and materials and generate maintenance/replacement/end-of-life obligations. The audit retains semiconductor fabrication, operational and lifecycle stages plus burden incidence, but general IEA/TSMC/e-waste context cannot substitute for same-object deployment measurement. Pinzone-style LCA remains model-based evidence with its own system boundary and uncertainty semantics."
