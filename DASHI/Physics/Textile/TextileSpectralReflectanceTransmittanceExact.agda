module DASHI.Physics.Textile.TextileSpectralReflectanceTransmittanceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Physics.Textile.TextileEmpiricalCalibrationExact as Calibration
import DASHI.Physics.Textile.TextileOpticalTransportBridgeExact as Optical
import DASHI.Topology.TextileStitchHyperfabricExact as Stitch

------------------------------------------------------------------------
-- PROVENANCE / SCOPE
--
-- NIST Spectral Reflectance and Transmittance maintains SI-traceable scales
-- for spectral reflectance and transmittance.  NIST measurement guidance also
-- distinguishes regular/specular and hemispherical collection geometries,
-- especially for scattering materials.
--
-- This module therefore keeps wavelength/spectral band, illumination,
-- collection geometry, and polarization as explicit calibration coordinates.
------------------------------------------------------------------------

nistSpectralRTSourceTitle : String
nistSpectralRTSourceTitle = "NIST Spectral Reflectance and Transmittance"

data CollectionGeometry : Set where
  regularDirectional : CollectionGeometry
  directionalHemispherical : CollectionGeometry
  customCollectionGeometry : CollectionGeometry

record SpectralRTMeasurementGeometry : Set where
  constructor spectral-rt-measurement-geometry
  field
    spectralBand : String
    illuminationGeometry : String
    collectionGeometry : CollectionGeometry
    collectionDescription : String
    polarisationConvention : String

open SpectralRTMeasurementGeometry public

record TextileSpectralRTCalibration
    {OpticalState Illumination OpticalObserver Radiance Scalar : Set}
    {topology : Stitch.StitchState}
    (model : Optical.TextileOpticalModel
      OpticalState Illumination OpticalObserver Radiance topology) : Set₁ where
  constructor textile-spectral-rt-calibration
  field
    specimen : Calibration.SpecimenIdentity
    sameSpecimenAsOpticalModel : specimen ≡ Optical.specimen model

    authority : String
    geometry : SpectralRTMeasurementGeometry

    spectralReflectance : Scalar
    spectralTransmittance : Scalar
    reportedUncertainty : String

open TextileSpectralRTCalibration public

------------------------------------------------------------------------
-- Opacity is retained only as a consumer-defined reduction of the measured
-- transmittance coordinate.  No universal complement law is assumed because
-- scattering/absorption conventions and detector geometry remain relevant.
------------------------------------------------------------------------

record TextileOpacityObservation
    {OpticalState Illumination OpticalObserver Radiance Scalar : Set}
    {topology : Stitch.StitchState}
    {model : Optical.TextileOpticalModel
      OpticalState Illumination OpticalObserver Radiance topology}
    (calibration : TextileSpectralRTCalibration {Scalar = Scalar} model) : Set₁ where
  constructor textile-opacity-observation
  field
    opacityFromTransmittance : Scalar → Scalar
    reportedOpacity : Scalar
    opacityLaw :
      reportedOpacity
      ≡ opacityFromTransmittance (spectralTransmittance calibration)

open TextileOpacityObservation public

------------------------------------------------------------------------
-- Non-promotion boundaries.
------------------------------------------------------------------------

data OneOpacityNumberDeterminesSpectralTransmittance : Set where

oneOpacityNumberDoesNotDetermineSpectralTransmittance :
  OneOpacityNumberDeterminesSpectralTransmittance → ⊥
oneOpacityNumberDoesNotDetermineSpectralTransmittance ()

data RegularTransmittanceEqualsHemisphericalTransmittanceByDefinition : Set where

regularTransmittanceDoesNotEqualHemisphericalByDefinition :
  RegularTransmittanceEqualsHemisphericalTransmittanceByDefinition → ⊥
regularTransmittanceDoesNotEqualHemisphericalByDefinition ()

data ReflectanceAndTransmittanceDetermineAbsorptanceWithoutClosureAssumptions : Set where

reflectanceAndTransmittanceDoNotDetermineAbsorptanceWithoutClosureAssumptions :
  ReflectanceAndTransmittanceDetermineAbsorptanceWithoutClosureAssumptions → ⊥
reflectanceAndTransmittanceDoNotDetermineAbsorptanceWithoutClosureAssumptions ()
