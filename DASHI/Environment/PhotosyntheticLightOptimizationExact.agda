module DASHI.Environment.PhotosyntheticLightOptimizationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Environment.CanopySpectralRadiativeTransferExact as Canopy
import DASHI.Environment.PhotosyntheticLightTransportCrossPollinationExact as Photo
import DASHI.Physics.Optics.InverseCausticNumericalProducerExact as Numerical

------------------------------------------------------------------------
-- PHOTOSYNTHETIC LIGHT OPTIMISATION
--
-- This is not a new photosynthesis model. It consumes the canonical
-- PhotosyntheticOpticsPlantWeld and adds a canopy-level optimisation surface.
-- The biological objective is assimilation under independently retained
-- thermal, hydraulic and photoinhibition constraints, not raw photon density.
------------------------------------------------------------------------

record PhotosyntheticObjective
    {LeafPoint Wavelength PhotonFlux ObjectiveValue : Set}
    {leaf : DASHI.Environment.PlantHydraulicAtmosphereCarbonCouplingExact.LeafGasExchangeReceipt}
    {calibration : DASHI.Environment.ConstitutiveHydrologyPlantCalibrationExact.LeafCarbonWaterCalibration leaf}
    {field : Photo.PhotosyntheticPhotonField LeafPoint Wavelength PhotonFlux}
    {interception : Photo.LeafLightInterceptionReceipt field}
    (weld : Photo.PhotosyntheticOpticsPlantWeld leaf calibration field interception) : Set₁ where
  constructor photosynthetic-objective
  field
    objective : Photo.CoupledState weld → ObjectiveValue
    objectiveIsAssimilationBased : String
    actionSpectrumReference : String
    leafAbsorptanceReference : String
    canopyAggregationReference : String
    waterCarbonCouplingReference : String

open PhotosyntheticObjective public

record BiologicalLightConstraints
    {State ConstraintValue : Set}
    (stateCarrier : State → ConstraintValue) : Set₁ where
  constructor biological-light-constraints
  field
    photoinhibitionRisk : State → ConstraintValue
    leafThermalLoad : State → ConstraintValue
    waterStressRisk : State → ConstraintValue
    spectralImbalanceRisk : State → ConstraintValue
    photoinhibitionLimit : ConstraintValue
    thermalLimit : ConstraintValue
    waterStressLimit : ConstraintValue
    spectralImbalanceLimit : ConstraintValue
    constraintAuthorityReference : String

open BiologicalLightConstraints public

record PhotosyntheticLightOptimisationCandidate
    {LeafPoint Wavelength PhotonFlux ObjectiveValue : Set}
    {leaf : DASHI.Environment.PlantHydraulicAtmosphereCarbonCouplingExact.LeafGasExchangeReceipt}
    {calibration : DASHI.Environment.ConstitutiveHydrologyPlantCalibrationExact.LeafCarbonWaterCalibration leaf}
    {field : Photo.PhotosyntheticPhotonField LeafPoint Wavelength PhotonFlux}
    {interception : Photo.LeafLightInterceptionReceipt field}
    {weld : Photo.PhotosyntheticOpticsPlantWeld leaf calibration field interception}
    (objective : PhotosyntheticObjective weld) : Set₁ where
  constructor photosynthetic-light-optimisation-candidate
  field
    candidateDescription : String
    opticalDesignArtifact : String
    opticalArtifactDigest : String
    retainedPlantOpticsWeld : Photo.PhotosyntheticOpticsPlantWeld leaf calibration field interception
    retainedPlantOpticsWeldIsSameObject : retainedPlantOpticsWeld ≡ weld
    predictedObjective : ObjectiveValue
    optimisationMethod : String
    optimisationRunReceipt : String

open PhotosyntheticLightOptimisationCandidate public

record PhotosyntheticLightOptimisationAdmission
    {LeafPoint Wavelength PhotonFlux ObjectiveValue : Set}
    {leaf : DASHI.Environment.PlantHydraulicAtmosphereCarbonCouplingExact.LeafGasExchangeReceipt}
    {calibration : DASHI.Environment.ConstitutiveHydrologyPlantCalibrationExact.LeafCarbonWaterCalibration leaf}
    {field : Photo.PhotosyntheticPhotonField LeafPoint Wavelength PhotonFlux}
    {interception : Photo.LeafLightInterceptionReceipt field}
    {weld : Photo.PhotosyntheticOpticsPlantWeld leaf calibration field interception}
    {objective : PhotosyntheticObjective weld}
    (candidate : PhotosyntheticLightOptimisationCandidate objective) : Set₁ where
  constructor photosynthetic-light-optimisation-admission
  field
    farquharCalibrationEvidence : String
    stomatalCalibrationEvidence : String
    lightResponseCalibrationEvidence : String
    photoinhibitionConstraintEvidence : String
    thermalConstraintEvidence : String
    waterConstraintEvidence : String
    siteFibreEvidence : String
    heldOutValidationPlan : String

open PhotosyntheticLightOptimisationAdmission public

------------------------------------------------------------------------
-- Canopy solver weld: the canopy transport model must compile into the same
-- canonical photon field/interception objects used by the plant weld.
------------------------------------------------------------------------

record CanopyOptimisationWeld
    {LeafPoint Wavelength Direction PhotonFlux ObjectiveValue : Set}
    {leaf : DASHI.Environment.PlantHydraulicAtmosphereCarbonCouplingExact.LeafGasExchangeReceipt}
    {calibration : DASHI.Environment.ConstitutiveHydrologyPlantCalibrationExact.LeafCarbonWaterCalibration leaf}
    {field : Photo.PhotosyntheticPhotonField LeafPoint Wavelength PhotonFlux}
    {interception : Photo.LeafLightInterceptionReceipt field}
    {weld : Photo.PhotosyntheticOpticsPlantWeld leaf calibration field interception}
    (canopy : Canopy.SpectralCanopyRadiationModel Wavelength Direction LeafPoint PhotonFlux)
    (canopyWeld : Canopy.CanopyToPhotosyntheticPhotonFieldWeld canopy field interception) : Set₁ where
  constructor canopy-optimisation-weld
  field
    samePhotonFieldReference : String
    sameLeafGeometryReference : String
    sameTimeSupportReference : String
    sameSiteConditionReference : String

open CanopyOptimisationWeld public

------------------------------------------------------------------------
-- Inverse-caustic x-pollination: the biological layer supplies the target;
-- the numerical optical producer still owes all independent optical residuals.
------------------------------------------------------------------------

record BiologicalTargetToInverseCausticWeld
    {SourceModel TargetPattern : Set}
    (problem : Numerical.InverseCausticProblem SourceModel TargetPattern) : Set₁ where
  constructor biological-target-to-inverse-caustic-weld
  field
    biologicalTargetReference : String
    targetPatternIsPhotosyntheticObjectiveRealisation : String
    sourceSpectrumAndGeometryReference : String
    downstreamPlantCalibrationReference : String

open BiologicalTargetToInverseCausticWeld public

------------------------------------------------------------------------
-- Non-promotion boundaries.
------------------------------------------------------------------------

data MoreAbsorbedLightAlwaysMeansMoreAssimilation : Set where
moreAbsorbedLightDoesNotAlwaysMeanMoreAssimilation :
  MoreAbsorbedLightAlwaysMeansMoreAssimilation → ⊥
moreAbsorbedLightDoesNotAlwaysMeanMoreAssimilation ()

data OpticalTargetMatchProvesPhotosyntheticBenefit : Set where
opticalTargetMatchDoesNotProvePhotosyntheticBenefit :
  OpticalTargetMatchProvesPhotosyntheticBenefit → ⊥
opticalTargetMatchDoesNotProvePhotosyntheticBenefit ()

data C3CalibrationIsUniversalPlantLightResponse : Set where
c3CalibrationIsNotUniversalPlantLightResponse :
  C3CalibrationIsUniversalPlantLightResponse → ⊥
c3CalibrationIsNotUniversalPlantLightResponse ()
