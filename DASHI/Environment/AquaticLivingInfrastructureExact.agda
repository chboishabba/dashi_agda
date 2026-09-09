module DASHI.Environment.AquaticLivingInfrastructureExact where

open import DASHI.Core.Prelude

import DASHI.Physics.Units.SI as SI
import DASHI.Environment.QuantitiesConservation as Conservation
import DASHI.Environment.FunctionalEcology as Ecology
import DASHI.Environment.EcologicalEvidenceGates as Evidence
import DASHI.Environment.AquaticLivingInfrastructureSourceRegistryExact as Sources

------------------------------------------------------------------------
-- AQUARIUM / REEF / BRACKISH / AQUACULTURE / HYDROPONIC LIVING FABRIC
--
-- Source-attribution boundary:
-- external engineering/biological source claims are carried through Sources;
-- this coupled fabric, its same-object welds and all no-shortcut barriers are
-- repository-native DASHI formal reconstruction / cross-domain synthesis.
------------------------------------------------------------------------

data WaterRegime : Set where
  freshwater
  brackish
  marine : WaterRegime

data SystemMode : Set where
  freshwaterAquarium
  brackishAquarium
  reefAquarium
  recirculatingAquaculture
  hydroponicSystem
  aquaponicSystem
  salineAquaponicSystem : SystemMode

data HydroponicMode : Set where
  mediaBedEbbFlow
  nutrientFilmTechnique
  deepWaterCulture
  dripSubstrate : HydroponicMode

data HydraulicRole : Set where
  vessel
  sump
  pipe
  valve
  drain
  overflow
  circulationPump
  returnPump
  bellSiphon : HydraulicRole

data TreatmentRole : Set where
  mechanicalSolidsSeparation
  biologicalFiltration
  foamFractionation
  aeration
  oxygenInjection
  degassing
  plantNutrientRecovery
  microbialMineralisation : TreatmentRole

data MediaRole : Set where
  rootSupportMedia
  attachedGrowthBiofilterMedia
  mechanicalFilterMedia
  habitatSubstrate : MediaRole

data CriticalLoad : Set where
  circulationLoad
  aerationLoad
  oxygenationLoad
  heatingCoolingLoad
  controlSensorLoad
  lightingLoad : CriticalLoad

data WaterQualityCoordinate : Set where
  temperature
  dissolvedOxygen
  pH
  salinityOrConductivity
  ammoniaTAN
  nitrite
  nitrate
  alkalinity
  suspendedSolids : WaterQualityCoordinate

------------------------------------------------------------------------
-- Water state. Regime is a categorical operating fibre; actual salinity or
-- conductivity remains an independently measured coordinate.
------------------------------------------------------------------------

record AquaticWaterState : Set where
  constructor aquatic-water-state
  field
    regime : WaterRegime
    temperatureReference : String
    dissolvedOxygenReference : String
    pHReference : String
    salinityOrConductivityReference : String
    ammoniaReference : String
    nitriteReference : String
    nitrateReference : String
    alkalinityReference : String
    solidsReference : String
    measurementProvenance : Evidence.EvidenceSource

open AquaticWaterState public

------------------------------------------------------------------------
-- Hydraulics and pumps.
------------------------------------------------------------------------

record HydraulicCircuit : Set where
  constructor hydraulic-circuit
  field
    roles : List HydraulicRole
    targetFlow : SI.Quantity SI.VolumetricFlowRate SI.unitScale
    deliveredFlow : SI.Quantity SI.VolumetricFlowRate SI.unitScale
    operatingPressure : SI.Quantity SI.Pressure SI.unitScale
    pumpElectricalPower : SI.Quantity SI.Power SI.unitScale
    pumpCurveReference : String
    staticHeadReference : String
    plumbingLossReference : String
    deliveredFlowMeasurementReference : String
    overflowAndDrainSafetyReference : String

open HydraulicCircuit public

record BellSiphonCycle : Set where
  constructor bell-siphon-cycle
  field
    hydroponicMode : HydroponicMode
    standpipeGeometryReference : String
    inflowReference : String
    floodLevelReference : String
    siphonTriggerReference : String
    drainRateReference : String
    breakAndResetReference : String
    emergencyOverflowReference : String
    cycleMeasurementReference : String
    source : Sources.AquaticSourceReference

open BellSiphonCycle public

------------------------------------------------------------------------
-- Gas transfer and treatment are distinct from hydraulics.
------------------------------------------------------------------------

record GasTransferSystem : Set where
  constructor gas-transfer-system
  field
    treatments : List TreatmentRole
    gasTransferDeviceReference : String
    airflowOrOxygenInputReference : String
    dissolvedOxygenResponseReference : String
    carbonDioxideDegassingReference : String
    transferEfficiencyReference : String
    monitoringReference : String

open GasTransferSystem public

record FiltrationTrain : Set where
  constructor filtration-train
  field
    treatments : List TreatmentRole
    mediaRoles : List MediaRole
    solidsCaptureReference : String
    biofilterMediaReference : String
    nitrificationCapacityReference : String
    mineralisationReference : String
    foamFractionationReference : String
    maintenanceAndBackwashReference : String
    measuredPerformanceReference : String

open FiltrationTrain public

record ProteinSkimmerRealisation : Set where
  constructor protein-skimmer-realisation
  field
    source : Sources.AquaticSourceReference
    gasLiquidContactReference : String
    foamProductionReference : String
    skimmateExportReference : String
    targetColloidOrDissolvedFractionReference : String
    measuredRemovalReference : String
    salinityAndWaterChemistryContext : String

open ProteinSkimmerRealisation public

------------------------------------------------------------------------
-- Electrical continuity / batteries.
------------------------------------------------------------------------

record BackupPowerSystem : Set where
  constructor backup-power-system
  field
    storedEnergy : SI.Quantity SI.Energy SI.unitScale
    deliverablePower : SI.Quantity SI.Power SI.unitScale
    criticalLoads : List CriticalLoad
    loadProfileReference : String
    inverterOrConverterReference : String
    transferControlReference : String
    autonomyReference : String
    batteryStateOfHealthReference : String
    periodicFailoverTestReference : String

open BackupPowerSystem public

record PowerContinuityReceipt
    (backup : BackupPowerSystem) : Set where
  constructor power-continuity-receipt
  field
    declaredLoadsCoveredReference : String
    measuredOrCalculatedAutonomyReference : String
    transferTestReference : String
    downstreamDeviceHealthReference : String

open PowerContinuityReceipt public

------------------------------------------------------------------------
-- Flora / fauna / microbial guilds.
------------------------------------------------------------------------

record AquaticBioticAssembly : Set where
  constructor aquatic-biotic-assembly
  field
    flora : List Ecology.SpeciesRefinement
    fauna : List Ecology.SpeciesRefinement
    functionalGroups : List Ecology.FunctionalGroup
    microbialGuildReference : String
    stockingOrPlantingDensityReference : String
    salinityCompatibilityEvidence : List Evidence.EvidenceSource
    temperatureCompatibilityEvidence : List Evidence.EvidenceSource
    oxygenCompatibilityEvidence : List Evidence.EvidenceSource
    trophicInteractionReference : String
    biosecurityReference : String

open AquaticBioticAssembly public

------------------------------------------------------------------------
-- Hydroponic root zone / media.
------------------------------------------------------------------------

record HydroponicRootZone : Set where
  constructor hydroponic-root-zone
  field
    mode : HydroponicMode
    supportMedia : List MediaRole
    rootZoneFlowReference : String
    wetDryCycleReference : String
    rootOxygenReference : String
    nutrientSolutionReference : String
    solidsCloggingReference : String
    plantUptakeMeasurementReference : String

open HydroponicRootZone public

------------------------------------------------------------------------
-- Whole living system.
------------------------------------------------------------------------

record AquaticLivingSystem : Set₁ where
  constructor aquatic-living-system
  field
    mode : SystemMode
    water : AquaticWaterState
    hydraulics : HydraulicCircuit
    gasTransfer : GasTransferSystem
    filtration : FiltrationTrain
    biota : AquaticBioticAssembly
    hydroponicRootZone : HydroponicRootZone
    backupPower : BackupPowerSystem
    conservation : Conservation.ConservationBundle
    sourceReferences : List Sources.AquaticSourceReference
    siteHistoryReference : String
    operatingProtocolReference : String
    alarmAndMonitoringReference : String

open AquaticLivingSystem public

------------------------------------------------------------------------
-- Aquaponics is an explicit weld, not a label-level identity.
------------------------------------------------------------------------

record AquaponicWeld (system : AquaticLivingSystem) : Set₁ where
  constructor aquaponic-weld
  field
    aquacultureFaunaReference : String
    sameRecirculatingWaterReference : String
    solidsSeparationReference : String
    microbialNitrogenConversionReference : String
    plantRootZoneReference : String
    dissolvedNutrientAvailabilityReference : String
    plantNutrientUptakeReference : String
    waterReturnReference : String
    nitrogenBalance : Conservation.NitrogenBalance
    phosphorusBalance : Conservation.PhosphorusBalance
    waterBalance : Conservation.WaterBalance
    sourceBoundaryReference : String

open AquaponicWeld public

------------------------------------------------------------------------
-- Source-specific adapters.
------------------------------------------------------------------------

canonicalBellSiphonSource : Sources.AquaticSourceReference
canonicalBellSiphonSource = Sources.bellSiphonHydraulics2026

canonicalSkimmerSource : Sources.AquaticSourceReference
canonicalSkimmerSource = Sources.proteinSkimmingLekang2019

canonicalSalineAquaponicsSource : Sources.AquaticSourceReference
canonicalSalineAquaponicsSource = Sources.salineAquaponicsReview2022

------------------------------------------------------------------------
-- WrongType / non-promotion barriers.
------------------------------------------------------------------------

data NominalPumpFlowMeansDeliveredFlowPermission : Set where
data PumpRunningMeansSafeDOPermission : Set where
data AerationMeansCirculationPermission : Set where
data CirculationMeansAerationPermission : Set where
data MechanicalMeansBiologicalFiltrationPermission : Set where
data BiofilterMediaMeansNitrificationCapacityPermission : Set where
data ProteinSkimmerMeansUniversalFiltrationPermission : Set where
data BellSiphonMeansPumpPermission : Set where
data BellSiphonMeansNutrientRemovalPermission : Set where
data BatteryEnergyMeansRuntimePermission : Set where
data BackupBatteryMeansFailSafePermission : Set where
data SalinityRegimeMeansSpeciesCompatibilityPermission : Set where
data FreshwaterCompatibilityMeansMarineCompatibilityPermission : Set where
data AquacultureMeansAquaponicsPermission : Set where
data AquaponicsMeansClosedNutrientLoopPermission : Set where
data SameWaterReadingMeansSameSystemHealthPermission : Set where

nominalPumpFlowDoesNotProveDeliveredFlow : NominalPumpFlowMeansDeliveredFlowPermission → ⊥
nominalPumpFlowDoesNotProveDeliveredFlow ()

pumpRunningDoesNotProveSafeDO : PumpRunningMeansSafeDOPermission → ⊥
pumpRunningDoesNotProveSafeDO ()

aerationDoesNotDefinitionallyProvideCirculation : AerationMeansCirculationPermission → ⊥
aerationDoesNotDefinitionallyProvideCirculation ()

circulationDoesNotDefinitionallyProvideAeration : CirculationMeansAerationPermission → ⊥
circulationDoesNotDefinitionallyProvideAeration ()

mechanicalFiltrationIsNotBiologicalFiltration : MechanicalMeansBiologicalFiltrationPermission → ⊥
mechanicalFiltrationIsNotBiologicalFiltration ()

biofilterMediaDoesNotByItselfCertifyNitrificationCapacity : BiofilterMediaMeansNitrificationCapacityPermission → ⊥
biofilterMediaDoesNotByItselfCertifyNitrificationCapacity ()

proteinSkimmerIsNotUniversalFiltration : ProteinSkimmerMeansUniversalFiltrationPermission → ⊥
proteinSkimmerIsNotUniversalFiltration ()

bellSiphonIsNotPump : BellSiphonMeansPumpPermission → ⊥
bellSiphonIsNotPump ()

bellSiphonDoesNotDefinitionallyRemoveNutrients : BellSiphonMeansNutrientRemovalPermission → ⊥
bellSiphonDoesNotDefinitionallyRemoveNutrients ()

batteryEnergyDoesNotDetermineRuntimeWithoutLoad : BatteryEnergyMeansRuntimePermission → ⊥
batteryEnergyDoesNotDetermineRuntimeWithoutLoad ()

backupBatteryDoesNotMakeWholeSystemFailSafe : BackupBatteryMeansFailSafePermission → ⊥
backupBatteryDoesNotMakeWholeSystemFailSafe ()

salinityLabelDoesNotProveSpeciesCompatibility : SalinityRegimeMeansSpeciesCompatibilityPermission → ⊥
salinityLabelDoesNotProveSpeciesCompatibility ()

freshwaterCompatibilityDoesNotTransferToMarine : FreshwaterCompatibilityMeansMarineCompatibilityPermission → ⊥
freshwaterCompatibilityDoesNotTransferToMarine ()

aquacultureDoesNotDefinitionallyEqualAquaponics : AquacultureMeansAquaponicsPermission → ⊥
aquacultureDoesNotDefinitionallyEqualAquaponics ()

aquaponicsDoesNotProveClosedNutrientLoop : AquaponicsMeansClosedNutrientLoopPermission → ⊥
aquaponicsDoesNotProveClosedNutrientLoop ()

sameWaterReadingDoesNotProveSameSystemHealth : SameWaterReadingMeansSameSystemHealthPermission → ⊥
sameWaterReadingDoesNotProveSameSystemHealth ()

record AquaticLivingInfrastructureBoundary : Set where
  constructor aquatic-living-infrastructure-boundary
  field
    salinityHydraulicsGasTransferFiltrationBiotaAndPowerRemainDistinct : Bool
    nominalAndDeliveredPumpPerformanceRemainDistinct : Bool
    mechanicalAndBiologicalFiltrationRemainDistinct : Bool
    skimmingIsSpecificSeparationMechanism : Bool
    bellSiphonIsHydraulicCycleComponent : Bool
    batteryEnergyPowerRuntimeRemainDistinct : Bool
    aquaponicsRequiresExplicitCrossDomainWeld : Bool
    waterNutrientBalancesRemainExplicit : Bool
    sourceClaimsAndDashiSynthesisRemainDistinct : Bool
    componentPresenceAutomaticallyProvesSystemViability : Bool

canonicalAquaticLivingInfrastructureBoundary : AquaticLivingInfrastructureBoundary
canonicalAquaticLivingInfrastructureBoundary =
  aquatic-living-infrastructure-boundary
    true true true true true true true true true false
