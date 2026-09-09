module DASHI.Environment.HolzerKrameterhofIntegratedLandscapeBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Environment.HolzerKrameterhofSourceAttributionExact as Sources
import DASHI.Environment.AquaticLivingInfrastructureExact as Aquatic
import DASHI.Environment.QuantitiesConservation as Conservation
import DASHI.Environment.YeomansKeylineLandscapeHydrologyExact as Keyline
import DASHI.Environment.SustainableManagementCausalEstimandExperimentBridgeExact as Causal
import DASHI.Environment.LESSituatedObservationInteractionExact as LES

------------------------------------------------------------------------
-- KRAMETERHOF INTEGRATED LANDSCAPE PRACTICE -> EXISTING LES FIBRES
--
-- This owner does not create a Holzer-specific world engine.  It records the
-- practice identity seen in the supplied farm-tour source and requires explicit
-- welds into existing aquatic, water-accounting, Keyline-comparison and causal
-- surfaces.
------------------------------------------------------------------------

data KrameterhofPracticeElement : Set where
  terraceCropping
  altitudeStaggeredCropping
  cascadingPondSystem
  gravityWaterDistribution
  mixedDepthPondHabitat
  fishCrayfishAquaculture
  plantedRestPond
  openChannelReaeration
  adjustablePondStandpipe
  terraceAgroforestry
  coppiceWithStandardsWoodland
  terraceEmbankmentGrazing
  rotationalPigGrazing
  passiveEarthCellarStorage
  microHydroPotential : KrameterhofPracticeElement

record SituatedKrameterhofPractice : Set where
  constructor situated-krameterhof-practice
  field
    source : Sources.KrameterhofSource
    element : KrameterhofPracticeElement
    siteHistoryReference : String
    topographyReference : String
    implementationReference : String
    timingReference : String
    sourceSpanReference : String

open SituatedKrameterhofPractice public

------------------------------------------------------------------------
-- Pond-cascade evidence packet.
--
-- The transcript reports repeatedly used water, vegetated rest ponds and open
-- channels as regeneration/oxygenation steps.  These are kept as intervention
-- identities and measurement obligations rather than encoded as successful
-- treatment effects.
------------------------------------------------------------------------

record PondCascadeEvidencePacket
    (practice : SituatedKrameterhofPractice) : Set where
  constructor pond-cascade-evidence-packet
  field
    waterBalance : Conservation.WaterBalance
    upperPondToLowerPondFlowReference : String
    overflowOrStandpipeReference : String
    openChannelGeometryReference : String
    plantedRestPondReference : String
    dissolvedOxygenBeforeReference : String
    dissolvedOxygenAfterReference : String
    temperatureReference : String
    pHReference : String
    ammoniaNitriteNitrateReference : String
    suspendedSolidsReference : String
    biologicalCommunityReference : String
    commonWaterIdentityReference : String
    commonSpatialBoundaryReference : String
    commonTemporalBoundaryReference : String
    uncertaintyReference : String

open PondCascadeEvidencePacket public

------------------------------------------------------------------------
-- Aquatic x-pollination.
--
-- A Krameterhof open channel may be tested as an aeration mechanism and a
-- vegetated rest pond may be tested as a treatment/biological-filtration stage,
-- but the pre-existing aquatic owner remains authoritative.  Presence of the
-- device/vegetation does not instantiate measured treatment performance.
------------------------------------------------------------------------

record KrameterhofAquaticTreatmentWeld
    {practice : SituatedKrameterhofPractice}
    (packet : PondCascadeEvidencePacket practice) : Set where
  constructor krameterhof-aquatic-treatment-weld
  field
    WaterState : Set
    beforeWater : WaterState
    afterWater : WaterState
    treatmentRoles : List Aquatic.TreatmentRole
    hydraulicRoles : List Aquatic.HydraulicRole
    dissolvedOxygenObservationReference : String
    nitrogenTransformationObservationReference : String
    solidsObservationReference : String
    waterIdentityPreservedReference : String
    existingAquaticOwnerReference : String
    measuredPerformanceRequired : Bool

open KrameterhofAquaticTreatmentWeld public

------------------------------------------------------------------------
-- Keyline comparison without lineage collapse.
--
-- Krameterhof and Keyline can share physical coordinates such as elevation,
-- storage, gravity distribution, contour/terrace geometry and earthworks.  The
-- same physical coordinate is not enough to identify the management practice.
------------------------------------------------------------------------

record KrameterhofKeylinePhysicalComparison : Set where
  constructor krameterhof-keyline-physical-comparison
  field
    krameterhof : SituatedKrameterhofPractice
    keyline : Keyline.KeylineLandscapeIntervention
    sharedPhysicalCoordinateReference : String
    krameterhofSourceReference : String
    keylineSourceReference : String
    implementationDifferenceReference : String
    managementLineageDifferenceReference : String
    causalComparisonRequiresMatchedEstimand : Bool

open KrameterhofKeylinePhysicalComparison public

------------------------------------------------------------------------
-- Existing causal-estimand adapter.
------------------------------------------------------------------------

krameterhofInterventionIdentity :
  SituatedKrameterhofPractice → Causal.SituatedInterventionIdentity
krameterhofInterventionIdentity practice =
  Causal.situated-intervention-identity
    Causal.landManagementPractice
    (implementationReference practice)
    (siteHistoryReference practice)
    (timingReference practice)
    "DASHI.Environment.HolzerKrameterhofSourceAttributionExact"

record KrameterhofLESExperiment : Set where
  constructor krameterhof-les-experiment
  field
    practice : SituatedKrameterhofPractice
    before : LES.SituatedObservation
    after : LES.SituatedObservation
    interventionIdentity : Causal.SituatedInterventionIdentity
    identityMatchesPractice :
      interventionIdentity ≡ krameterhofInterventionIdentity practice
    comparatorReference : String
    assignmentOrIdentificationReference : String
    outcomeMeasurementReference : String
    sourceDataProvenanceReference : String
    uncertaintyReference : String

open KrameterhofLESExperiment public

------------------------------------------------------------------------
-- WrongType / no-shortcut barriers.
------------------------------------------------------------------------

data PondCascadeMeansRASPermission : Set where
data OpenChannelMeansCertifiedAerationPermission : Set where
data PlantedPondMeansCertifiedBiofilterPermission : Set where
data WaterReuseMeansClosedLoopPermission : Set where
data GravityFedMeansZeroEnergyPermission : Set where
data TerraceMeansInfiltrationGainPermission : Set where
data PigRootingMeansSoilImprovementPermission : Set where
data MultipleUseMeansNetBenefitPermission : Set where
data RegenerationLabelMeansWaterQualityRestoredPermission : Set where
data KrameterhofMeansKeylinePermission : Set where
data SamePhysicalInterventionMeansSameManagementPracticePermission : Set where
data SameMeasuredOutcomeMeansSameProvenancePermission : Set where

pondCascadeDoesNotDefinitionallyMeanRAS : PondCascadeMeansRASPermission → ⊥
pondCascadeDoesNotDefinitionallyMeanRAS ()

openChannelDoesNotByItselfCertifyAeration : OpenChannelMeansCertifiedAerationPermission → ⊥
openChannelDoesNotByItselfCertifyAeration ()

plantedPondDoesNotByItselfCertifyBiofiltration : PlantedPondMeansCertifiedBiofilterPermission → ⊥
plantedPondDoesNotByItselfCertifyBiofiltration ()

waterReuseDoesNotProveClosedLoop : WaterReuseMeansClosedLoopPermission → ⊥
waterReuseDoesNotProveClosedLoop ()

gravityFedDoesNotMeanZeroEnergy : GravityFedMeansZeroEnergyPermission → ⊥
gravityFedDoesNotMeanZeroEnergy ()

terracePresenceDoesNotProveInfiltrationGain : TerraceMeansInfiltrationGainPermission → ⊥
terracePresenceDoesNotProveInfiltrationGain ()

pigRootingDoesNotProveSoilImprovement : PigRootingMeansSoilImprovementPermission → ⊥
pigRootingDoesNotProveSoilImprovement ()

multipleUseDoesNotAutomaticallyProveNetBenefit : MultipleUseMeansNetBenefitPermission → ⊥
multipleUseDoesNotAutomaticallyProveNetBenefit ()

regenerationLabelDoesNotProveRestoredWaterQuality :
  RegenerationLabelMeansWaterQualityRestoredPermission → ⊥
regenerationLabelDoesNotProveRestoredWaterQuality ()

krameterhofIsNotDefinitionallyKeyline : KrameterhofMeansKeylinePermission → ⊥
krameterhofIsNotDefinitionallyKeyline ()

samePhysicalInterventionDoesNotIdentifyManagementPractice :
  SamePhysicalInterventionMeansSameManagementPracticePermission → ⊥
samePhysicalInterventionDoesNotIdentifyManagementPractice ()

sameMeasuredOutcomeDoesNotEraseProvenance :
  SameMeasuredOutcomeMeansSameProvenancePermission → ⊥
sameMeasuredOutcomeDoesNotEraseProvenance ()

record KrameterhofIntegratedBoundary : Set where
  constructor krameterhof-integrated-boundary
  field
    pondTerraceLivestockAgroforestryAndStorageRemainDistinctCoordinates : Bool
    existingAquaticHydrologyAndCausalOwnersRemainAuthoritative : Bool
    practitionerClaimsRequireIndependentMeasurementForEffects : Bool
    samePhysicalInterventionDoesNotEraseManagementLineage : Bool
    sameOutcomeDoesNotEraseSourceProvenance : Bool
    waterReuseAutomaticallyProvesWaterQuality : Bool
    gravityAutomaticallyMeansZeroExternalCost : Bool

canonicalKrameterhofIntegratedBoundary : KrameterhofIntegratedBoundary
canonicalKrameterhofIntegratedBoundary =
  krameterhof-integrated-boundary true true true true true false false
