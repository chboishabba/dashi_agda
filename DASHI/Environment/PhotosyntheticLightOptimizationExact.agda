module DASHI.Environment.PhotosyntheticLightOptimizationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Environment.CanopySpectralRadiativeTransferExact as Canopy
import DASHI.Environment.ConstitutiveHydrologyPlantCalibrationExact as Calibration
import DASHI.Environment.PlantHydraulicAtmosphereCarbonCouplingExact as Plant
import DASHI.Physics.Optics.InverseCausticNumericalProducerExact as Numerical

------------------------------------------------------------------------
-- PHOTOSYNTHETIC LIGHT OPTIMISATION
--
-- This is not a new photosynthesis model. It binds a wavelength/angle-resolved
-- canopy light producer to the existing leaf-gas-exchange and calibration
-- surfaces, then exposes an optimisation objective subject to biological and
-- thermal constraints.
------------------------------------------------------------------------

record PhotosyntheticObjective
    {Wavelength Direction CanopyPoint PhotonFlux ObjectiveValue : Set}
    (canopy : Canopy.SpectralCanopyRadiationModel
      Wavelength Direction CanopyPoint PhotonFlux)
    (leaf : Plant.LeafGasExchangeReceipt) : Set₁ where
  constructor photosynthetic-objective
  field
    EvaluationState : Set
    leafState : EvaluationState → Plant.LeafState leaf
    atmosphereState : EvaluationState → Plant.AtmosphereState leaf
    canopyPoint : EvaluationState → CanopyPoint
    objective : EvaluationState → ObjectiveValue
    objectiveDefinitionReference : String
    actionSpectrumReference : String
    leafAbsorptanceReference : String
    aggregationReference : String

open PhotosyntheticObjective public

record BiologicalLightConstraints
    {State ConstraintValue : Set}
    (objective : State → ConstraintValue) : Set₁ where
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
    {Wavelength Direction CanopyPoint PhotonFlux ObjectiveValue ConstraintValue : Set}
    {leaf : Plant.LeafGasExchangeReceipt}
    (canopy : Canopy.SpectralCanopyRadiationModel
      Wavelength Direction CanopyPoint PhotonFlux)
    (objective : PhotosyntheticObjective canopy leaf) : Set₁ where
  constructor photosynthetic-light-optimisation-candidate
  field
    candidateDescription : String
    opticalDesignArtifact : String
    opticalArtifactDigest : String
    retainedCanopyModel :
      Canopy.SpectralCanopyRadiationModel
        Wavelength Direction CanopyPoint PhotonFlux
    retainedCanopyModelIsSameObject : retainedCanopyModel ≡ canopy
    predictedObjective : ObjectiveValue
    optimisationMethod : String
    optimisationRunReceipt : String

open PhotosyntheticLightOptimisationCandidate public

record PhotosyntheticLightOptimisationAdmission
    {Wavelength Direction CanopyPoint PhotonFlux ObjectiveValue ConstraintValue : Set}
    {leaf : Plant.LeafGasExchangeReceipt}
    {canopy : Canopy.SpectralCanopyRadiationModel
      Wavelength Direction CanopyPoint PhotonFlux}
    {objective : PhotosyntheticObjective canopy leaf}
    (candidate : PhotosyntheticLightOptimisationCandidate canopy objective) : Set₁ where
  constructor photosynthetic-light-optimisation-admission
  field
    sameLeafAndCanopyGeometryEvidence : String
    farquharCalibrationEvidence : String
    stomatalCalibrationEvidence : String
    lightResponseCalibrationEvidence : String
    photoinhibitionConstraintEvidence : String
    thermalConstraintEvidence : String
    waterConstraintEvidence : String
    heldOutValidationPlan : String

open PhotosyntheticLightOptimisationAdmission public

------------------------------------------------------------------------
-- Cross-pollination into inverse caustic design: a biological objective may
-- provide a target illumination pattern, but the numerical optical producer
-- still has to satisfy its independent geometric/residual obligations.
------------------------------------------------------------------------

record BiologicalTargetToInverseCausticWeld
    {SourceModel TargetPattern SourceRay SurfacePoint TargetPoint Normal Flux Scalar : Set}
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
