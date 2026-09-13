module DASHI.Environment.PhotosyntheticLightTransportCrossPollinationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Architecture.SemiconductorBuiltEnvironmentCrossPollinationExact as Semiconductor
import DASHI.Environment.ConstitutiveHydrologyPlantCalibrationExact as Calibration
import DASHI.Environment.LESPhysicalProcessSourceRegistryExact as Sources
import DASHI.Environment.PlantHydraulicAtmosphereCarbonCouplingExact as Plant
import DASHI.Environment.SolarOpticalSiteFibreCrossPollinationExact as Site
import DASHI.Physics.Optics.AsphericCausticManipulationExact as Caustic
import DASHI.Physics.Optics.InverseCausticNumericalProducerExact as Numerical
import DASHI.Physics.Units.SI as SI

------------------------------------------------------------------------
-- SOURCE ATTRIBUTION
--
-- Farquhar/von Caemmerer/Berry remains the existing LES authority for the C3
-- biochemical assimilation architecture. McCree supplies the separate optical
-- action-spectrum / photosynthetically-active-radiation calibration boundary.
-- DASHI owns the cross-domain weld below. ASML/semiconductor design-execution
-- content is reused only as an engineering analogy for calibrated model ->
-- realised geometry -> measured outcome; it is not biology authority.
------------------------------------------------------------------------

farquharC3Source : Sources.SourceReference
farquharC3Source = Sources.farquharVonCaemmererBerry1980

mcCreeActionSpectrumSource : Sources.SourceReference
mcCreeActionSpectrumSource = Sources.sourceReference
  "K. J. McCree"
  "The action spectrum, absorptance and quantum yield of photosynthesis in crop plants"
  "Agricultural Meteorology 9, 191-216"
  1972
  "DOI 10.1016/0002-1571(71)90022-7"
  Sources.journalArticle
  Sources.c3PhotosynthesisArchitecture
  "Source calibration for wavelength-dependent leaf photosynthetic action spectrum, absorptance and quantum yield over measured crop species; motivates retaining wavelength-resolved photon input rather than generic optical intensity alone."
  "Does not define universal spectral response across all species, developmental states, environments or C3/C4/CAM pathways, and does not imply an optical hotspot increases carbon assimilation."

------------------------------------------------------------------------
-- OPTICAL INPUT FIBRE
--
-- Photosynthesis consumes a biologically interpreted photon field, not merely
-- generic radiance. Spatial position, wavelength, direction/interception and
-- time/support remain explicit coordinates.
------------------------------------------------------------------------

record PhotosyntheticPhotonField
    (LeafPoint Wavelength PhotonFlux : Set) : Set₁ where
  constructor photosynthetic-photon-field
  field
    incidentPhotonFlux : LeafPoint → Wavelength → PhotonFlux
    photosyntheticActionWeight : Wavelength → PhotonFlux
    absorbedPhotonFlux : LeafPoint → Wavelength → PhotonFlux
    canopyGeometryReference : String
    leafOrientationReference : String
    spectralCalibrationReference : String
    photonFluxCalibrationReference : String
    actionSpectrumSource : Sources.SourceReference

open PhotosyntheticPhotonField public

record LeafLightInterceptionReceipt
    {LeafPoint Wavelength PhotonFlux : Set}
    (field : PhotosyntheticPhotonField LeafPoint Wavelength PhotonFlux) : Set₁ where
  constructor leaf-light-interception-receipt
  field
    LeafOpticalState : Set
    leafPoint : LeafOpticalState → LeafPoint
    interceptedSpectrum : LeafOpticalState → Wavelength → PhotonFlux
    interceptionLawReference : String
    absorptionLawReference : String
    selfShadingReference : String
    neighbourShadingReference : String
    validationReference : String

open LeafLightInterceptionReceipt public

------------------------------------------------------------------------
-- SAME-STATE WELD TO THE EXISTING LES LEAF/CARBON MODEL
------------------------------------------------------------------------

record PhotosyntheticOpticsPlantWeld
    {LeafPoint Wavelength PhotonFlux : Set}
    (leaf : Plant.LeafGasExchangeReceipt)
    (calibration : Calibration.LeafCarbonWaterCalibration leaf)
    (field : PhotosyntheticPhotonField LeafPoint Wavelength PhotonFlux)
    (interception : LeafLightInterceptionReceipt field) : Set₁ where
  constructor photosynthetic-optics-plant-weld
  field
    CoupledState : Set
    plantCalibrationState : CoupledState → Calibration.LeafCalibrationState calibration
    opticalState : CoupledState → LeafOpticalState interception

    commonLeafGeometryReference : String
    commonTimeSupportReference : String
    illuminationToLightResponseSameObjectReference : String
    spectralResponseCalibrationReference : String
    carbonAssimilationObservationReference : String
    heldOutOpticalBiologicalValidationReference : String

open PhotosyntheticOpticsPlantWeld public

carbonAssimilationAt :
  ∀ {LeafPoint Wavelength PhotonFlux : Set}
    {leaf : Plant.LeafGasExchangeReceipt}
    {calibration : Calibration.LeafCarbonWaterCalibration leaf}
    {field : PhotosyntheticPhotonField LeafPoint Wavelength PhotonFlux}
    {interception : LeafLightInterceptionReceipt field} →
    (weld : PhotosyntheticOpticsPlantWeld leaf calibration field interception) →
    CoupledState weld →
    SI.Quantity SI.MolarFluxDensity (Plant.gasFluxScale leaf)
carbonAssimilationAt {leaf = leaf} {calibration = calibration} weld state =
  Plant.carbonAssimilationFlux leaf
    (Calibration.leafState calibration (plantCalibrationState weld state))
    (Calibration.atmosphereState calibration (plantCalibrationState weld state))

------------------------------------------------------------------------
-- SITE FIBRE WELD
--
-- Reuse the existing LES solar/optical site carrier because its coordinates
-- are exactly the environmental coordinates required here: spectrum, angle,
-- temperature, shading, soiling, wind, humidity, support and provenance.
-- No photovoltaic response law is inherited by this reuse.
------------------------------------------------------------------------

record SiteConditionedPhotosynthesisRealisation
    {SiteId Spectrum AngleDistribution Temperature Shading Soiling Wind Humidity : Set}
    {LeafPoint Wavelength PhotonFlux : Set}
    (siteFibre : Site.SolarOpticalSiteFibre
      SiteId Spectrum AngleDistribution Temperature Shading Soiling Wind Humidity)
    (leaf : Plant.LeafGasExchangeReceipt)
    (calibration : Calibration.LeafCarbonWaterCalibration leaf)
    (field : PhotosyntheticPhotonField LeafPoint Wavelength PhotonFlux)
    (interception : LeafLightInterceptionReceipt field)
    (weld : PhotosyntheticOpticsPlantWeld leaf calibration field interception) : Set₁ where
  constructor site-conditioned-photosynthesis-realisation
  field
    retainedSiteFibre : Site.SolarOpticalSiteFibre
      SiteId Spectrum AngleDistribution Temperature Shading Soiling Wind Humidity
    retainedSiteFibreIsSameObject : retainedSiteFibre ≡ siteFibre
    retainedPlantOpticsWeld : PhotosyntheticOpticsPlantWeld leaf calibration field interception
    retainedPlantOpticsWeldIsSameObject : retainedPlantOpticsWeld ≡ weld
    siteSpectrumToPhotonFieldReference : String
    incidenceAngleToInterceptionReference : String
    siteTemperatureToLeafStateReference : String
    windHumidityToAtmosphereStateReference : String
    shadingSoilingToPhotonFieldReference : String
    waterAvailabilityReference : String
    atmosphericCO2Reference : String
    siteSpecificHeldOutValidationReference : String

open SiteConditionedPhotosynthesisRealisation public

------------------------------------------------------------------------
-- OPTIONAL INVERSE-LIGHT-SHAPING CONSUMER
--
-- A certified inverse-caustic solution may target a photon-field objective,
-- but the target itself must be supplied by the plant/experiment layer. The
-- optical optimiser is not permitted to invent the biological objective.
------------------------------------------------------------------------

record PhotosyntheticInverseLightShapingReceipt
    {SourceModel TargetPattern SourceRay SurfacePoint TargetPoint Normal Flux Scalar : Set}
    {problem : Numerical.InverseCausticProblem SourceModel TargetPattern}
    {surface : Caustic.OpticalSurfaceGeometry SurfacePoint Normal}
    {rayMap : Caustic.CausticRayMap SourceRay SurfacePoint TargetPoint Flux}
    {algebra : Numerical.ResidualAlgebra Scalar}
    {candidate : Numerical.NumericalInverseCausticCandidate {Scalar = Scalar} problem surface rayMap}
    {thresholds : Numerical.NumericalAdmissionThresholds algebra}
    (solution : Numerical.CertifiedInverseCausticNumericalSolution algebra candidate thresholds) : Set₁ where
  constructor photosynthetic-inverse-light-shaping-receipt
  field
    biologicalTargetDefinitionReference : String
    targetPatternIsPhotonFieldObjective : String
    plantCalibrationReference : String
    opticalSolutionRetained : Numerical.CertifiedInverseCausticNumericalSolution algebra candidate thresholds
    opticalSolutionIsSameObject : opticalSolutionRetained ≡ solution
    photonConservationReference : String
    thermalConstraintReference : String
    photoinhibitionConstraintReference : String
    siteConditionReference : String
    predictedAssimilationComparisonReference : String

open PhotosyntheticInverseLightShapingReceipt public

------------------------------------------------------------------------
-- ASML / SEMICONDUCTOR X-POLLINATION IS ARCHITECTURAL ONLY.
------------------------------------------------------------------------

record PrecisionOpticsDesignExecutionAnalogy : Set₁ where
  constructor precision-optics-design-execution-analogy
  field
    semiconductorDesignExecutionOwner : Semiconductor.DesignExecutionSystem
    calibratedForwardModelReference : String
    inverseCorrectionReference : String
    precisionRealisationReference : String
    metrologyFeedbackReference : String
    photosyntheticOpticsReuseBoundary : String

open PrecisionOpticsDesignExecutionAnalogy public

------------------------------------------------------------------------
-- NON-PROMOTION BOUNDARIES
------------------------------------------------------------------------

data MoreIncidentLightAlwaysMeansMorePhotosynthesis : Set where
moreIncidentLightDoesNotAlwaysMeanMorePhotosynthesis :
  MoreIncidentLightAlwaysMeansMorePhotosynthesis → ⊥
moreIncidentLightDoesNotAlwaysMeanMorePhotosynthesis ()

data CausticHotspotProvesHigherCarbonAssimilation : Set where
causticHotspotDoesNotProveHigherCarbonAssimilation :
  CausticHotspotProvesHigherCarbonAssimilation → ⊥
causticHotspotDoesNotProveHigherCarbonAssimilation ()

data OpticalUniformityDeterminesBiologicalOptimum : Set where
opticalUniformityDoesNotDetermineBiologicalOptimum :
  OpticalUniformityDeterminesBiologicalOptimum → ⊥
opticalUniformityDoesNotDetermineBiologicalOptimum ()

data SameOpticImpliesSamePhotosyntheticOutcomeAcrossSites : Set where
sameOpticDoesNotImplySamePhotosyntheticOutcomeAcrossSites :
  SameOpticImpliesSamePhotosyntheticOutcomeAcrossSites → ⊥
sameOpticDoesNotImplySamePhotosyntheticOutcomeAcrossSites ()

data ASMLArchitectureIsPhotosynthesisAuthority : Set where
asmlArchitectureIsNotPhotosynthesisAuthority : ASMLArchitectureIsPhotosynthesisAuthority → ⊥
asmlArchitectureIsNotPhotosynthesisAuthority ()

data LightShapingCreatesPhotons : Set where
lightShapingDoesNotCreatePhotons : LightShapingCreatesPhotons → ⊥
lightShapingDoesNotCreatePhotons ()

data OpticalValidationAloneClosesPlantOutcome : Set where
opticalValidationAloneDoesNotClosePlantOutcome : OpticalValidationAloneClosesPlantOutcome → ⊥
opticalValidationAloneDoesNotClosePlantOutcome ()
