module DASHI.Environment.SolarOpticalSiteFibreCrossPollinationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Environment.ValidationGovernance as Governance
import DASHI.Environment.CertifiedValidationGovernanceExact as Certified
import DASHI.Physics.Optics.OpticalSurfaceManufacturingToleranceExact as Manufacturing

------------------------------------------------------------------------
-- LES / SOLAR / OPTICAL SITE FIBRE
--
-- The Living Environment System contract keeps environmental fields,
-- observations, uncertainty and provenance separate from an engineered asset.
-- This module reuses that separation for optical / photovoltaic deployment.
-- It is not a universal photovoltaic performance law.
------------------------------------------------------------------------

lesLatentEnvironmentStateSource : String
lesLatentEnvironmentStateSource =
  "chboishabba/Living-Environment-System, docs/latent-environment-state.md"

record SolarOpticalSiteFibre
    (Site Spectrum AngleDistribution Temperature Shading Soiling Wind Humidity : Set) : Set₁ where
  constructor solar-optical-site-fibre
  field
    site : Site
    spectralIrradiance : Spectrum
    incidenceAngleDistribution : AngleDistribution
    moduleOrSurfaceTemperature : Temperature
    shadingState : Shading
    soilingState : Soiling
    windState : Wind
    humidityState : Humidity
    spatialSupport : String
    temporalSupport : String
    uncertainty : String
    provenance : String

open SolarOpticalSiteFibre public

record SiteConditionedOpticalEnergyObservation
    {Site Spectrum AngleDistribution Temperature Shading Soiling Wind Humidity Output : Set}
    (fibre : SolarOpticalSiteFibre Site Spectrum AngleDistribution Temperature Shading Soiling Wind Humidity) : Set₁ where
  constructor site-conditioned-optical-energy-observation
  field
    engineeredArtifactIdentity : String
    artifactOpticalCalibration : String
    observedOutput : Output
    observationProtocol : String
    observationUncertainty : String
    observationProvenance : String

open SiteConditionedOpticalEnergyObservation public

record SameArtifactDifferentSiteResponse
    {Site Spectrum AngleDistribution Temperature Shading Soiling Wind Humidity Output : Set}
    (left right : SolarOpticalSiteFibre Site Spectrum AngleDistribution Temperature Shading Soiling Wind Humidity)
    (leftObservation : SiteConditionedOpticalEnergyObservation {Output = Output} left)
    (rightObservation : SiteConditionedOpticalEnergyObservation {Output = Output} right) : Set₁ where
  constructor same-artifact-different-site-response
  field
    sameEngineeredArtifact :
      engineeredArtifactIdentity leftObservation
      ≡ engineeredArtifactIdentity rightObservation
    siteFibresDistinct : left ≡ right → ⊥
    outputsDistinct :
      observedOutput leftObservation ≡ observedOutput rightObservation → ⊥

open SameArtifactDifferentSiteResponse public

record GovernedSolarOpticalDeployment
    {Site Spectrum AngleDistribution Temperature Shading Soiling Wind Humidity Output : Set}
    (fibre : SolarOpticalSiteFibre Site Spectrum AngleDistribution Temperature Shading Soiling Wind Humidity)
    (observation : SiteConditionedOpticalEnergyObservation {Output = Output} fibre)
    (gate : Governance.DeploymentGate) : Set₁ where
  constructor governed-solar-optical-deployment
  field
    retainedSiteFibre : SolarOpticalSiteFibre Site Spectrum AngleDistribution Temperature Shading Soiling Wind Humidity
    retainedSiteFibreIsSameObject : retainedSiteFibre ≡ fibre
    retainedObservation : SiteConditionedOpticalEnergyObservation fibre
    retainedObservationIsSameObject : retainedObservation ≡ observation
    certifiedDeployment : Certified.CertifiedDeploymentGate gate

open GovernedSolarOpticalDeployment public

------------------------------------------------------------------------
-- Non-promotion boundaries.
------------------------------------------------------------------------

data SameArtifactImpliesSameSiteOutput : Set where
sameArtifactDoesNotImplySameSiteOutput : SameArtifactImpliesSameSiteOutput → ⊥
sameArtifactDoesNotImplySameSiteOutput ()

data LaboratoryOpticalValidationImpliesSiteSuitability : Set where
laboratoryOpticalValidationDoesNotImplySiteSuitability :
  LaboratoryOpticalValidationImpliesSiteSuitability → ⊥
laboratoryOpticalValidationDoesNotImplySiteSuitability ()

data OpticalEfficiencyImpliesEcologicalApproval : Set where
opticalEfficiencyDoesNotImplyEcologicalApproval : OpticalEfficiencyImpliesEcologicalApproval → ⊥
opticalEfficiencyDoesNotImplyEcologicalApproval ()

data SiteObservationDeterminesUniversalPVLaw : Set where
siteObservationDoesNotDetermineUniversalPVLaw : SiteObservationDeterminesUniversalPVLaw → ⊥
siteObservationDoesNotDetermineUniversalPVLaw ()
