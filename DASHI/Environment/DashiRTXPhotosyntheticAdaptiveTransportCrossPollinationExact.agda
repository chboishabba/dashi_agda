module DASHI.Environment.DashiRTXPhotosyntheticAdaptiveTransportCrossPollinationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Environment.CanopySpectralRadiativeTransferExact as Canopy
import DASHI.Environment.ConstitutiveHydrologyPlantCalibrationExact as Calibration
import DASHI.Environment.PhotosyntheticLightTransportCrossPollinationExact as Photo
import DASHI.Environment.PhotosyntheticLightOptimizationExact as Optimisation
import DASHI.Environment.PlantHydraulicAtmosphereCarbonCouplingExact as Plant
import DASHI.Physics.Optics.DashiRTXAdaptiveTransportSourceAtlasExact as RTXSource

record AdaptiveTransportAlgebra (Scalar : Set) : Set₁ where
  constructor adaptive-transport-algebra
  field
    zero one : Scalar
    add multiply : Scalar → Scalar → Scalar
    _≤_ : Scalar → Scalar → Set

open AdaptiveTransportAlgebra public

record AuthoritativeCanopyKernelReceipt
    {Wavelength Direction CanopyPoint PhotonFlux : Set}
    (canopy : Canopy.SpectralCanopyRadiationModel Wavelength Direction CanopyPoint PhotonFlux) : Set₁ where
  constructor authoritative-canopy-kernel-receipt
  field
    kernelAuthorityReference : String
    transportEquationReference : String
    discretisationReference : String
    conservationReference : String
    numericalValidationReference : String
    retainedCanopyModel : Canopy.SpectralCanopyRadiationModel Wavelength Direction CanopyPoint PhotonFlux
    retainedCanopyModelIsSameObject : retainedCanopyModel ≡ canopy

open AuthoritativeCanopyKernelReceipt public

record DashiRTXAdaptiveAllocationReceipt
    {Cell Scalar : Set}
    (algebra : AdaptiveTransportAlgebra Scalar) : Set₁ where
  constructor dashi-rtx-adaptive-allocation-receipt
  field
    transportError : Cell → Scalar
    signedFrontier : Cell → Scalar
    importance : Cell → Scalar
    persistentState : Cell → Scalar
    refreshProbability : Cell → Scalar
    chosenRefresh : Cell → Bool
    mdlObjectiveValue : Scalar
    refinementBudget : Scalar
    implementation : RTXSource.DashiRTXArtifactReference
    runDigest : String
    configurationDigest : String

open DashiRTXAdaptiveAllocationReceipt public

record PhotosyntheticImportanceAdapter
    {Cell LeafPoint Wavelength PhotonFlux Scalar : Set}
    {field : Photo.PhotosyntheticPhotonField LeafPoint Wavelength PhotonFlux}
    (allocationImportance : Cell → Scalar) : Set₁ where
  constructor photosynthetic-importance-adapter
  field
    cellToLeafPointReference : String
    photonFieldSameObjectReference : String
    assimilationSensitivityReference : String
    photoinhibitionRiskReference : String
    thermalRiskReference : String
    waterStressRiskReference : String
    biologicalImportance : Cell → Scalar
    importanceAdapterLawReference : String

open PhotosyntheticImportanceAdapter public

record AdaptiveCanopyTransportWeld
    {Wavelength Direction CanopyPoint PhotonFlux LeafPoint Scalar Cell : Set}
    {canopy : Canopy.SpectralCanopyRadiationModel Wavelength Direction CanopyPoint PhotonFlux}
    {field : Photo.PhotosyntheticPhotonField LeafPoint Wavelength PhotonFlux}
    {interception : Photo.LeafLightInterceptionReceipt field}
    (kernel : AuthoritativeCanopyKernelReceipt canopy)
    (canopyWeld : Canopy.CanopyToPhotosyntheticPhotonFieldWeld canopy field interception)
    (algebra : AdaptiveTransportAlgebra Scalar)
    (allocation : DashiRTXAdaptiveAllocationReceipt {Cell = Cell} algebra) : Set₁ where
  constructor adaptive-canopy-transport-weld
  field
    adaptiveStrategySourceBoundary : RTXSource.DashiRTXSourceBoundary
    retainedKernel : AuthoritativeCanopyKernelReceipt canopy
    retainedKernelIsSameObject : retainedKernel ≡ kernel
    retainedCanopyWeld : Canopy.CanopyToPhotosyntheticPhotonFieldWeld canopy field interception
    retainedCanopyWeldIsSameObject : retainedCanopyWeld ≡ canopyWeld
    refinementActsOnKernelEvaluationReference : String
    refinementPreservesTransportSemanticsReference : String
    heldOutErrorReductionReference : String

open AdaptiveCanopyTransportWeld public

record AdaptivePhotosyntheticOptimisationWeld
    {LeafPoint Wavelength PhotonFlux ObjectiveValue Scalar Cell : Set}
    {leaf : Plant.LeafGasExchangeReceipt}
    {calibration : Calibration.LeafCarbonWaterCalibration leaf}
    {field : Photo.PhotosyntheticPhotonField LeafPoint Wavelength PhotonFlux}
    {interception : Photo.LeafLightInterceptionReceipt field}
    {weld : Photo.PhotosyntheticOpticsPlantWeld leaf calibration field interception}
    (objective : Optimisation.PhotosyntheticObjective weld)
    (importance : Cell → Scalar) : Set₁ where
  constructor adaptive-photosynthetic-optimisation-weld
  field
    importanceAdapter : PhotosyntheticImportanceAdapter {field = field} importance
    objectiveSensitivityReference : String
    budgetAllocationReference : String
    refinementStoppingCriterionReference : String
    predictedObjectiveErrorReference : String
    heldOutAssimilationValidationReference : String

open AdaptivePhotosyntheticOptimisationWeld public

data DashiRTXIsAuthoritativeCanopyRadiativeTransfer : Set where
dashiRTXIsNotAuthoritativeCanopyRadiativeTransfer :
  DashiRTXIsAuthoritativeCanopyRadiativeTransfer → ⊥
dashiRTXIsNotAuthoritativeCanopyRadiativeTransfer ()

data RenderingErrorImportanceIsBiologicalImportance : Set where
renderingErrorImportanceDoesNotEqualBiologicalImportanceByDefinition :
  RenderingErrorImportanceIsBiologicalImportance → ⊥
renderingErrorImportanceDoesNotEqualBiologicalImportanceByDefinition ()

data AdaptiveRefreshProvesPhotosyntheticImprovement : Set where
adaptiveRefreshDoesNotProvePhotosyntheticImprovement :
  AdaptiveRefreshProvesPhotosyntheticImprovement → ⊥
adaptiveRefreshDoesNotProvePhotosyntheticImprovement ()

data SparseRefinementProvesUnbiasedTransport : Set where
sparseRefinementDoesNotProveUnbiasedTransport : SparseRefinementProvesUnbiasedTransport → ⊥
sparseRefinementDoesNotProveUnbiasedTransport ()
