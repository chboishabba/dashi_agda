module DASHI.Physics.Textile.TextileLustreObservationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Physics.Textile.TextileEmpiricalCalibrationExact as Calibration
import DASHI.Physics.Textile.TextileOpticalTransportBridgeExact as Optical
import DASHI.Topology.TextileStitchHyperfabricExact as Stitch

------------------------------------------------------------------------
-- PROVENANCE / SCOPE
--
-- Maria E. Nadal, E. A. Early, E. A. Thompson,
-- "Gloss Measurements at NIST", NCSL Workshop (1999).
-- NIST describes specular gloss as the appearance attribute producing a shiny
-- or lustrous appearance and measures it by comparison of specular luminous
-- reflectance with a primary standard.
--
-- This module therefore treats gloss/lustre as a calibrated, geometry- and
-- observer-conditioned observable.  It is not an intrinsic scalar determined
-- solely by a fiber material name.
------------------------------------------------------------------------

nistGlossSourceTitle : String
nistGlossSourceTitle = "Gloss Measurements at NIST"

record LustreMeasurementGeometry : Set where
  constructor lustre-measurement-geometry
  field
    illuminationGeometry : String
    observationGeometry : String
    spectralOrPhotometricResponse : String
    polarisationConvention : String

open LustreMeasurementGeometry public

record SpecularLustreCalibration
    {OpticalState Illumination OpticalObserver Radiance Scalar : Set}
    {topology : Stitch.StitchState}
    (model : Optical.TextileOpticalModel
      OpticalState Illumination OpticalObserver Radiance topology) : Set₁ where
  constructor specular-lustre-calibration
  field
    specimen : Calibration.SpecimenIdentity
    sameSpecimenAsOpticalModel : specimen ≡ Optical.specimen model

    authority : String
    geometry : LustreMeasurementGeometry

    specularLuminousReflectance : Scalar
    primaryStandardReflectance : Scalar
    reportedGlossOrLustre : Scalar

    compareToPrimaryStandard : Scalar → Scalar → Scalar
    calibrationLaw :
      reportedGlossOrLustre
      ≡ compareToPrimaryStandard
          specularLuminousReflectance
          primaryStandardReflectance

open SpecularLustreCalibration public

------------------------------------------------------------------------
-- An observer-relative appearance receipt keeps the actual radiance sample
-- separate from the reduced gloss/lustre statistic.
------------------------------------------------------------------------

record TextileLustreObservation
    {OpticalState Illumination OpticalObserver Radiance Scalar : Set}
    {topology : Stitch.StitchState}
    (model : Optical.TextileOpticalModel
      OpticalState Illumination OpticalObserver Radiance topology)
    (state : OpticalState)
    (observer : OpticalObserver) : Set₁ where
  constructor textile-lustre-observation
  field
    radiance : Optical.TextileRadianceObservation model state observer
    lustreCalibration : SpecularLustreCalibration {Scalar = Scalar} model

open TextileLustreObservation public

------------------------------------------------------------------------
-- Non-promotion boundaries.
------------------------------------------------------------------------

data GlossNumberIsIntrinsicMaterialConstant : Set where

glossNumberIsNotIntrinsicMaterialConstant :
  GlossNumberIsIntrinsicMaterialConstant → ⊥
glossNumberIsNotIntrinsicMaterialConstant ()

data SameGlossImpliesSameSpectralRadiance : Set where

sameGlossDoesNotImplySameSpectralRadiance :
  SameGlossImpliesSameSpectralRadiance → ⊥
sameGlossDoesNotImplySameSpectralRadiance ()

data SameRadianceAtOneObserverImpliesSameLustreAtAllGeometries : Set where

sameRadianceAtOneObserverDoesNotImplySameLustreAtAllGeometries :
  SameRadianceAtOneObserverImpliesSameLustreAtAllGeometries → ⊥
sameRadianceAtOneObserverDoesNotImplySameLustreAtAllGeometries ()

data MechanicalCalibrationDeterminesOpticalAppearance : Set where

mechanicalCalibrationDoesNotDetermineOpticalAppearance :
  MechanicalCalibrationDeterminesOpticalAppearance → ⊥
mechanicalCalibrationDoesNotDetermineOpticalAppearance ()
