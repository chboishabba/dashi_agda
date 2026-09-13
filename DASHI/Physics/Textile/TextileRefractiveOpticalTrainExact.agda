module DASHI.Physics.Textile.TextileRefractiveOpticalTrainExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Physics.Optics.GeometricalOpticsRefractionLensPrismExact as Geo
import DASHI.Physics.Textile.TextileOpticalTransportBridgeExact as Optical
import DASHI.Topology.TextileStitchHyperfabricExact as Stitch

------------------------------------------------------------------------
-- Refractive elements around a textile sample.
--
-- A prism, lens, window, immersion medium, or refracting interface belongs to
-- the illumination/observation train, not to the textile material itself.
-- This module keeps those coordinates explicit and composable around the
-- existing textile optical transport model.
------------------------------------------------------------------------

data RefractiveElementKind : Set where
  planarInterface : RefractiveElementKind
  prism : RefractiveElementKind
  convergingLens : RefractiveElementKind
  divergingLens : RefractiveElementKind
  refractiveWindow : RefractiveElementKind
  customRefractiveElement : RefractiveElementKind

record RefractiveOpticalElement
    {Scalar Wavelength : Set}
    (algebra : Geo.GeometricalOpticsAlgebra Scalar) : Set₁ where
  constructor refractive-optical-element
  field
    kind : RefractiveElementKind
    elementLabel : String
    materialCalibration : String
    geometryCalibration : String
    refractiveIndex : Wavelength → Scalar

open RefractiveOpticalElement public

record TextileOpticalTrain
    {OpticalState Illumination OpticalObserver Radiance Scalar Wavelength : Set}
    {topology : Stitch.StitchState}
    (model : Optical.TextileOpticalModel
      OpticalState Illumination OpticalObserver Radiance topology)
    (algebra : Geo.GeometricalOpticsAlgebra Scalar) : Set₁ where
  constructor textile-optical-train
  field
    illuminationSideElements : List (RefractiveOpticalElement {Wavelength = Wavelength} algebra)
    observationSideElements : List (RefractiveOpticalElement {Wavelength = Wavelength} algebra)
    retainedTextileModel :
      Optical.TextileOpticalModel
        OpticalState Illumination OpticalObserver Radiance topology
    retainedTextileModelIsSameObject : retainedTextileModel ≡ model

open TextileOpticalTrain public

record TextileRefractionReceipt
    {OpticalState Illumination OpticalObserver Radiance Scalar Wavelength : Set}
    {topology : Stitch.StitchState}
    {model : Optical.TextileOpticalModel
      OpticalState Illumination OpticalObserver Radiance topology}
    {algebra : Geo.GeometricalOpticsAlgebra Scalar}
    (train : TextileOpticalTrain {Wavelength = Wavelength} model algebra) : Set₁ where
  constructor textile-refraction-receipt
  field
    interfaceLaw : Geo.SnellRefractionReceipt algebra
    elementContext : String

open TextileRefractionReceipt public

record TextilePrismReceipt
    {OpticalState Illumination OpticalObserver Radiance Scalar Wavelength : Set}
    {topology : Stitch.StitchState}
    {model : Optical.TextileOpticalModel
      OpticalState Illumination OpticalObserver Radiance topology}
    {algebra : Geo.GeometricalOpticsAlgebra Scalar}
    (train : TextileOpticalTrain {Wavelength = Wavelength} model algebra) : Set₁ where
  constructor textile-prism-receipt
  field
    dispersion : Geo.PrismDispersionReceipt {Wavelength = Wavelength} algebra
    prismIsInOpticalTrain : String

open TextilePrismReceipt public

record TextileLensReceipt
    {OpticalState Illumination OpticalObserver Radiance Scalar Wavelength : Set}
    {topology : Stitch.StitchState}
    {model : Optical.TextileOpticalModel
      OpticalState Illumination OpticalObserver Radiance topology}
    {algebra : Geo.GeometricalOpticsAlgebra Scalar}
    (train : TextileOpticalTrain {Wavelength = Wavelength} model algebra) : Set₁ where
  constructor textile-lens-receipt
  field
    imaging : Geo.ThinLensReceipt algebra
    lensMaker : Geo.LensMakerReceipt algebra
    lensIsInOpticalTrain : String

open TextileLensReceipt public

------------------------------------------------------------------------
-- Non-promotion boundaries.
------------------------------------------------------------------------

data LensInObservationPathChangesIntrinsicTextileBRDF : Set where
lensInObservationPathDoesNotChangeIntrinsicTextileBRDF :
  LensInObservationPathChangesIntrinsicTextileBRDF → ⊥
lensInObservationPathDoesNotChangeIntrinsicTextileBRDF ()

data PrismDispersionIsTextileIridescence : Set where
prismDispersionIsNotTextileIridescence : PrismDispersionIsTextileIridescence → ⊥
prismDispersionIsNotTextileIridescence ()

data OpticalTrainCalibrationDeterminesTextileMaterialOptics : Set where
opticalTrainCalibrationDoesNotDetermineTextileMaterialOptics :
  OpticalTrainCalibrationDeterminesTextileMaterialOptics → ⊥
opticalTrainCalibrationDoesNotDetermineTextileMaterialOptics ()
