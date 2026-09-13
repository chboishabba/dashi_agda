module DASHI.Environment.HolzerPermacultureSurroundingCrossPollinationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Environment.HolzerKrameterhofSourceAttributionExact as HolzerSources
import DASHI.Environment.HolzerKrameterhofIntegratedLandscapeBridgeExact as Holzer
import DASHI.Environment.HolzerKrameterhofAdjacentSOTASourceRegistryExact as SOTA
import DASHI.Environment.AquaticLivingInfrastructureExact as Aquatic
import DASHI.Environment.YeomansKeylineLandscapeHydrologyExact as Keyline
import DASHI.Environment.PermacultureEmbodiedEnergyLandscapeBridgeExact as PermacultureEnergy
import DASHI.Environment.PluralSustainableLandManagementTraditionsExact as Plural
import DASHI.Environment.SustainableManagementCausalEstimandExperimentBridgeExact as Causal
import DASHI.Governance.PermacultureEvolution as PermacultureGovernance

------------------------------------------------------------------------
-- HOLZER <-> PERMACULTURE / SURROUNDING MANAGEMENT CROSS-POLLINATION
--
-- We cross-pollinate shared consumer coordinates, not lineage identities.
--
-- physical mechanism
--   != named tradition
--   != practitioner-reported practice
--   != adjacent literature
--   != measured effect
--   != DASHI cross-source inference
--   != recommendation.
------------------------------------------------------------------------

data SharedLandscapeMechanism : Set where
  surfaceWaterStorage
  gravityWaterRedistribution
  openChannelGasExchange
  plantedWaterTreatmentZone
  terraceRunoffInterception
  terraceSoilWaterRetention
  treeSlopeStabilisation
  treeLivestockSpatialCoupling
  biomassNutrientReturn
  passiveGroundThermalStorage
  altitudeSeasonExtension
  multifunctionalLandUse : SharedLandscapeMechanism

data CrossPollinationAxis : Set where
  hydrologyAxis
  aquaticTreatmentAxis
  agroforestryAxis
  livestockAxis
  soilCarbonAxis
  embodiedEnergyAxis
  passiveInfrastructureAxis
  governanceLineageAxis
  causalExperimentAxis : CrossPollinationAxis

data EvidenceAdmissionState : Set where
  practitionerOnly
  mechanismAdjacentLiterature
  matchedExternalStudy
  siteMeasured
  causallyEstimated
  replicatedOrHeldOut : EvidenceAdmissionState

------------------------------------------------------------------------
-- Same physical coordinate, different management provenance.
------------------------------------------------------------------------

record HolzerPermacultureMechanismProjection : Set where
  constructor holzer-permaculture-mechanism-projection
  field
    holzerPractice : Holzer.SituatedKrameterhofPractice
    sharedMechanism : SharedLandscapeMechanism
    axis : CrossPollinationAxis
    source : HolzerSources.KrameterhofSource
    permacultureTradition : PermacultureGovernance.PermacultureTradition
    traditionProjectionReference : String
    physicalProjectionReference : String
    lineageDifferenceReference : String
    dashiInferenceReference : String

open HolzerPermacultureMechanismProjection public

record HolzerPluralTraditionComparison : Set where
  constructor holzer-plural-tradition-comparison
  field
    holzerPractice : Holzer.SituatedKrameterhofPractice
    comparisonFamily : Plural.AdditionalPracticeFamily
    sharedMechanism : SharedLandscapeMechanism
    sharedConsumerCoordinateReference : String
    implementationDifferenceReference : String
    sourceLineageDifferenceReference : String
    directEquivalenceAsserted : Bool

open HolzerPluralTraditionComparison public

------------------------------------------------------------------------
-- Adjacent SOTA can pay mechanism plausibility / experiment design only.
------------------------------------------------------------------------

record HolzerAdjacentEvidenceAdmission : Set where
  constructor holzer-adjacent-evidence-admission
  field
    holzerPractice : Holzer.SituatedKrameterhofPractice
    adjacentSource : SOTA.AdjacentSOTASource
    sharedMechanism : SharedLandscapeMechanism
    admissionState : EvidenceAdmissionState
    interventionMatchReference : String
    siteClimateSoilMatchReference : String
    outcomeCoordinateMatchReference : String
    timeBoundaryMatchReference : String
    sourceRelationReference : String
    directKrameterhofValidation : Bool

open HolzerAdjacentEvidenceAdmission public

------------------------------------------------------------------------
-- Pond cascade <-> aquatic infrastructure.
------------------------------------------------------------------------

record PondCascadeAquaticCrossPollination
    {practice : Holzer.SituatedKrameterhofPractice}
    (packet : Holzer.PondCascadeEvidencePacket practice) : Set where
  constructor pond-cascade-aquatic-cross-pollination
  field
    candidateTreatmentRoles : List Aquatic.TreatmentRole
    candidateHydraulicRoles : List Aquatic.HydraulicRole
    beforeAfterDOReference : String
    nitrogenSpeciesReference : String
    solidsReference : String
    flowReference : String
    plantedZoneReference : String
    openChannelReference : String
    sameWaterBoundaryReference : String
    adjacentSOTA : List SOTA.AdjacentSOTASource
    mechanismEvidenceIsNotPerformanceReceipt : Bool

open PondCascadeAquaticCrossPollination public

------------------------------------------------------------------------
-- Holzer water management <-> Yeomans Keyline.
------------------------------------------------------------------------

record HolzerYeomansConsumerRelativeComparison : Set where
  constructor holzer-yeomans-consumer-relative-comparison
  field
    holzerPractice : Holzer.SituatedKrameterhofPractice
    keylinePractice : Keyline.KeylineLandscapeIntervention
    sharedMechanism : SharedLandscapeMechanism
    sharedWaterConsumerReference : String
    sharedSedimentConsumerReference : String
    sharedEnergyConsumerReference : String
    implementationIdentityDifferenceReference : String
    provenanceDifferenceReference : String
    sameConsumerResultWouldNotIdentifySamePractice : Bool

open HolzerYeomansConsumerRelativeComparison public

------------------------------------------------------------------------
-- Passive storage <-> embodied-energy / powered-storage comparison.
------------------------------------------------------------------------

record PassiveStorageEnergyComparison : Set where
  constructor passive-storage-energy-comparison
  field
    holzerPractice : Holzer.SituatedKrameterhofPractice
    landscapeStoredCapacityReference : String
    embodiedConstructionEnergyReference : String
    groundThermalCouplingReference : String
    ventilationReference : String
    humidityReference : String
    productTemperatureReference : String
    productLossReference : String
    poweredComparatorEnergyReference : String
    matchedStorageServiceReference : String
    adjacentStorageEvidence : List SOTA.AdjacentSOTASource
    energySavingRequiresMeasurementOrModel : Bool

open PassiveStorageEnergyComparison public

------------------------------------------------------------------------
-- Whole-farm management stack.
--
-- Multiple practices can coexist at one site without collapsing labels.  The
-- stack is an LES/counterfactual experiment object, not a claim that every
-- interaction is beneficial.
------------------------------------------------------------------------

record HolzerSurroundingManagementStack : Set where
  constructor holzer-surrounding-management-stack
  field
    holzerPractices : List Holzer.SituatedKrameterhofPractice
    surroundingFamilies : List Plural.AdditionalPracticeFamily
    permacultureGovernanceLenses : List PermacultureGovernance.PermacultureTradition
    physicalMechanisms : List SharedLandscapeMechanism
    interactionReceiptReferences : List String
    waterAccountingReference : String
    nutrientAccountingReference : String
    embodiedEnergyReference : String
    biodiversityOrHabitatReference : String
    labourCapitalMaintenanceReference : String
    sourceAttributionReference : String
    causalEstimandReference : String

open HolzerSurroundingManagementStack public

------------------------------------------------------------------------
-- No-shortcut / attribution firewalls.
------------------------------------------------------------------------

data SharedMechanismMeansSameTraditionPermission : Set where
data PermacultureLabelMeansHolzerPermission : Set where
data HolzerMeansPermacultureUniversalityPermission : Set where
data AdjacentWetlandEvidenceMeansPondCascadeValidationPermission : Set where
data SilvopastureEvidenceMeansHolzerAgroforestryValidationPermission : Set where
data PassiveCoolingLiteratureMeansKrameterhofEnergySavingPermission : Set where
data SameOutcomeMeansSameGovernancePermission : Set where
data WholeFarmStackMeansSynergyPermission : Set where

sharedMechanismDoesNotIdentifyTradition :
  SharedMechanismMeansSameTraditionPermission → ⊥
sharedMechanismDoesNotIdentifyTradition ()

permacultureLabelDoesNotIdentifyHolzerLineage :
  PermacultureLabelMeansHolzerPermission → ⊥
permacultureLabelDoesNotIdentifyHolzerLineage ()

holzerPracticeDoesNotProvePermacultureUniversality :
  HolzerMeansPermacultureUniversalityPermission → ⊥
holzerPracticeDoesNotProvePermacultureUniversality ()

constructedWetlandEvidenceDoesNotValidatePondCascade :
  AdjacentWetlandEvidenceMeansPondCascadeValidationPermission → ⊥
constructedWetlandEvidenceDoesNotValidatePondCascade ()

silvopastureEvidenceDoesNotValidateHolzerAgroforestry :
  SilvopastureEvidenceMeansHolzerAgroforestryValidationPermission → ⊥
silvopastureEvidenceDoesNotValidateHolzerAgroforestry ()

passiveCoolingLiteratureDoesNotPayKrameterhofEnergySaving :
  PassiveCoolingLiteratureMeansKrameterhofEnergySavingPermission → ⊥
passiveCoolingLiteratureDoesNotPayKrameterhofEnergySaving ()

sameOutcomeDoesNotEraseGovernanceOrLineage :
  SameOutcomeMeansSameGovernancePermission → ⊥
sameOutcomeDoesNotEraseGovernanceOrLineage ()

wholeFarmStackDoesNotDefinitionallyProveSynergy :
  WholeFarmStackMeansSynergyPermission → ⊥
wholeFarmStackDoesNotDefinitionallyProveSynergy ()

record HolzerPermacultureCrossPollinationBoundary : Set where
  constructor holzer-permaculture-cross-pollination-boundary
  field
    mechanismTraditionEvidenceAndOutcomeRemainDistinct : Bool
    holzerYeomansAndOtherPermacultureLineagesRemainDistinct : Bool
    adjacentLiteratureCanInformMechanismAndExperimentDesign : Bool
    adjacentLiteratureCannotDirectlyPayKrameterhofEffect : Bool
    wholeFarmInteractionsRequireExplicitReceipts : Bool
    samePhysicalConsumerCanCompareDifferentTraditions : Bool
    sameConsumerOutcomeDoesNotEraseProvenance : Bool
    dashiCrossSourceSynthesisRemainsDashiOwned : Bool

canonicalHolzerPermacultureCrossPollinationBoundary :
  HolzerPermacultureCrossPollinationBoundary
canonicalHolzerPermacultureCrossPollinationBoundary =
  holzer-permaculture-cross-pollination-boundary
    true true true true true true true true
