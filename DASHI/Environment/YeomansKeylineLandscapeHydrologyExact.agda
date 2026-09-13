module DASHI.Environment.YeomansKeylineLandscapeHydrologyExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Environment.YeomansKeylineSourceAttributionExact as Sources
import DASHI.Environment.QuantitiesConservation as Conservation
import DASHI.Environment.SoilPlantAtmosphereContinuumExact as SPAC
import DASHI.Environment.ConstitutiveHydrologyPlantCalibrationExact as Hydrology
import DASHI.Environment.LESSituatedObservationInteractionExact as LES

------------------------------------------------------------------------
-- KEYLINE LANDSCAPE/HYDROLOGY ADAPTER
--
-- Keyline is represented as a situated landscape intervention that changes
-- geometry, storage/routing and management.  The existing LES hydrology/SPAC
-- machinery remains authoritative for physical water-state evolution.
------------------------------------------------------------------------

data KeylineElement : Set where
  topographicSurvey
  keyPointKeylineGeometry
  offContourCultivation
  farmDamStorage
  diversionOrIrrigationChannel
  gravityIrrigation
  treeOrShelterLayout
  roadAndAccessLayout
  soilDevelopmentManagement : KeylineElement

data HydrologicConsumerCoordinate : Set where
  rainfallInput
  surfaceRouting
  infiltration
  rootZoneStorage
  damStorage
  irrigationDelivery
  runoffExport
  sedimentExport : HydrologicConsumerCoordinate

record KeylineLandscapeIntervention : Set where
  constructor keyline-landscape-intervention
  field
    source : Sources.KeylineSource
    element : KeylineElement
    siteHistoryReference : String
    topographyReference : String
    keypointOrContourGeometryReference : String
    implementationReference : String
    machineryOrEarthworkReference : String
    temporalHorizonReference : String

open KeylineLandscapeIntervention public

record KeylineWaterAccountingPacket
    (intervention : KeylineLandscapeIntervention) : Set where
  constructor keyline-water-accounting-packet
  field
    waterBalance : Conservation.WaterBalance
    sedimentBalance : Conservation.SedimentBalance
    resourceLedger : Conservation.ResourceLedger
    rainfallMeasurementReference : String
    runoffMeasurementOrModelReference : String
    infiltrationMeasurementOrModelReference : String
    storageMeasurementReference : String
    irrigationDeliveryReference : String
    commonSpatialBoundaryReference : String
    commonTemporalBoundaryReference : String
    uncertaintyReference : String

open KeylineWaterAccountingPacket public

------------------------------------------------------------------------
-- Reuse the exact constitutive hydrology owner.  Keyline geometry may alter
-- boundary conditions/routing; it does not replace Richards/Mualem/van
-- Genuchten calibration or silently make a surface-flow model equal to a
-- subsurface unsaturated-flow model.
------------------------------------------------------------------------

record KeylineConstitutiveHydrologyWeld
    (intervention : KeylineLandscapeIntervention)
    (soilLaw : Hydrology.SoilRetentionConductivityLaw)
    (flow : Hydrology.RichardsUnsaturatedFlowReceipt soilLaw)
    (calibration : Hydrology.SoilHydraulicCalibrationReceipt soilLaw flow)
    (soilBoundary : SPAC.SoilHydraulicBoundaryReceipt) : Set₁ where
  constructor keyline-constitutive-hydrology-weld
  field
    accounting : KeylineWaterAccountingPacket intervention
    geometryToSurfaceBoundaryReference : String
    surfaceRoutingToInfiltrationBoundaryReference : String
    infiltrationToConstitutiveStateReference : String
    constitutiveStateToSPACBoundaryReference : String
    soilBoundaryIdentityReference : String
    calibrationAppliesToSiteReference : String
    heldOutHydrologyValidationReference : String

open KeylineConstitutiveHydrologyWeld public

record KeylineSituatedObservationPacket
    (intervention : KeylineLandscapeIntervention) : Set where
  constructor keyline-situated-observation-packet
  field
    before : LES.SituatedObservation
    after : LES.SituatedObservation
    accounting : KeylineWaterAccountingPacket intervention
    interventionIdentityReference : String
    observationMethodReference : String
    comparatorReference : String

open KeylineSituatedObservationPacket public

------------------------------------------------------------------------
-- WrongType barriers.
------------------------------------------------------------------------

data KeylineGeometryMeansInfiltrationGainPermission : Set where
data DamStorageMeansRootZoneWaterPermission : Set where
data WaterCaptureMeansPlantUptakePermission : Set where
data SurfaceRoutingMeansRichardsFlowPermission : Set where
data SameWaterBalanceMeansSameCropOutcomePermission : Set where
data OneKeylineElementMeansFullSystemPermission : Set where
data DesignOrderingMeansOptimizationProofPermission : Set where

data SameContourMeansSameKeylineImplementationPermission : Set where

geometryDoesNotProveInfiltrationGain : KeylineGeometryMeansInfiltrationGainPermission → ⊥
geometryDoesNotProveInfiltrationGain ()
damStorageDoesNotDefinitionallyEqualRootZoneWater : DamStorageMeansRootZoneWaterPermission → ⊥
damStorageDoesNotDefinitionallyEqualRootZoneWater ()
waterCaptureDoesNotProvePlantUptake : WaterCaptureMeansPlantUptakePermission → ⊥
waterCaptureDoesNotProvePlantUptake ()
surfaceRoutingIsNotDefinitionallyRichardsFlow : SurfaceRoutingMeansRichardsFlowPermission → ⊥
surfaceRoutingIsNotDefinitionallyRichardsFlow ()
sameWaterLedgerDoesNotFixCropOutcome : SameWaterBalanceMeansSameCropOutcomePermission → ⊥
sameWaterLedgerDoesNotFixCropOutcome ()
oneElementDoesNotInstantiateWholeKeylineSystem : OneKeylineElementMeansFullSystemPermission → ⊥
oneElementDoesNotInstantiateWholeKeylineSystem ()
designOrderDoesNotBecomeOptimizationProof : DesignOrderingMeansOptimizationProofPermission → ⊥
designOrderDoesNotBecomeOptimizationProof ()
sameContourDoesNotIdentifyKeylineImplementation : SameContourMeansSameKeylineImplementationPermission → ⊥
sameContourDoesNotIdentifyKeylineImplementation ()

record KeylineHydrologyBoundary : Set where
  constructor keyline-hydrology-boundary
  field
    existingHydrologySolverRemainsAuthoritative : Bool
    waterSedimentResourceLedgersRemainDistinct : Bool
    topographyImplementationAndHistoryRemainFirstClass : Bool
    designSourceAndEmpiricalEffectRemainDistinct : Bool
    modeledHydrologyAutomaticallyCountsAsObservedEffect : Bool
    waterCaptureAutomaticallyMeansAgronomicBenefit : Bool

canonicalKeylineHydrologyBoundary : KeylineHydrologyBoundary
canonicalKeylineHydrologyBoundary =
  keyline-hydrology-boundary true true true true false false
