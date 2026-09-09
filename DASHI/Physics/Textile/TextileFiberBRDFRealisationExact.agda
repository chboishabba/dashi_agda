module DASHI.Physics.Textile.TextileFiberBRDFRealisationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Physics.Textile.TextileEmpiricalCalibrationExact as Calibration
import DASHI.Physics.Textile.TextileOpticalTransportBridgeExact as Optical
import DASHI.Topology.TextileStitchHyperfabricExact as Stitch

------------------------------------------------------------------------
-- PROVENANCE / SCOPE
--
-- Iman Sadeghi, Oleg Bisker, Joachim De Deken, Henrik Wann Jensen,
-- "A Practical Microcylinder Appearance Model for Cloth Rendering",
-- ACM Transactions on Graphics 32(2), 2013, DOI 10.1145/2451236.2451240.
--
-- Carlos Aliaga et al., "An Appearance Model for Textile Fibers",
-- Computer Graphics Forum 36(4), 2017, DOI 10.1111/cgf.13222.
--
-- These sources motivate retaining thread/fiber scattering, tangent direction,
-- weave structure, shadowing/masking, and multiscale optical response as
-- distinct coordinates.  This module provides a source-conditioned BRDF
-- realization interface; it does not claim either model is universal.
------------------------------------------------------------------------

microcylinderSourceDOI : String
microcylinderSourceDOI = "10.1145/2451236.2451240"

fiberAppearanceSourceDOI : String
fiberAppearanceSourceDOI = "10.1111/cgf.13222"

record TextileDirectionalGeometry
    (IncidentDirection OutgoingDirection : Set) : Set₁ where
  constructor textile-directional-geometry
  field
    incidentDirection : IncidentDirection
    outgoingDirection : OutgoingDirection
    fiberOrThreadTangentDescription : String
    yarnTwistDescription : String
    shadowingMaskingDescription : String

open TextileDirectionalGeometry public

record TextileFiberBRDFRealisation
    {OpticalState Illumination OpticalObserver Radiance Scalar : Set}
    {IncidentDirection OutgoingDirection : Set}
    {topology : Stitch.StitchState}
    (model : Optical.TextileOpticalModel
      OpticalState Illumination OpticalObserver Radiance topology) : Set₁ where
  constructor textile-fiber-brdf-realisation
  field
    specimen : Calibration.SpecimenIdentity
    sameSpecimenAsOpticalModel : specimen ≡ Optical.specimen model

    directionalGeometry :
      TextileDirectionalGeometry IncidentDirection OutgoingDirection

    measuredOrCalibratedThreadScattering : String
    weaveOrKnitAlignmentCalibration : String

    BRDF : IncidentDirection → OutgoingDirection → Scalar
    realisedDirectionalResponse : Scalar

    responseIsBRDFSample :
      realisedDirectionalResponse
      ≡ BRDF
          (incidentDirection directionalGeometry)
          (outgoingDirection directionalGeometry)

open TextileFiberBRDFRealisation public

record BRDFRadianceWeld
    {OpticalState Illumination OpticalObserver Radiance Scalar : Set}
    {IncidentDirection OutgoingDirection : Set}
    {topology : Stitch.StitchState}
    (model : Optical.TextileOpticalModel
      OpticalState Illumination OpticalObserver Radiance topology)
    (realisation : TextileFiberBRDFRealisation
      {Scalar = Scalar}
      {IncidentDirection = IncidentDirection}
      {OutgoingDirection = OutgoingDirection}
      model) : Set₁ where
  constructor brdf-radiance-weld
  field
    state : OpticalState
    observer : OpticalObserver
    radianceObservation :
      Optical.TextileRadianceObservation model state observer
    sourceConditionedOpticalLaw : String

open BRDFRadianceWeld public

------------------------------------------------------------------------
-- Non-promotion boundaries.
------------------------------------------------------------------------

data OneDirectionalBRDFSampleDeterminesFullFabricAppearance : Set where

oneDirectionalBRDFSampleDoesNotDetermineFullFabricAppearance :
  OneDirectionalBRDFSampleDeterminesFullFabricAppearance → ⊥
oneDirectionalBRDFSampleDoesNotDetermineFullFabricAppearance ()

data FiberBRDFAloneDeterminesFabricBRDF : Set where

fiberBRDFAloneDoesNotDetermineFabricBRDF :
  FiberBRDFAloneDeterminesFabricBRDF → ⊥
fiberBRDFAloneDoesNotDetermineFabricBRDF ()

data OneClothModelIsUniversalForAllTextiles : Set where

oneClothModelIsNotUniversalForAllTextiles :
  OneClothModelIsUniversalForAllTextiles → ⊥
oneClothModelIsNotUniversalForAllTextiles ()
