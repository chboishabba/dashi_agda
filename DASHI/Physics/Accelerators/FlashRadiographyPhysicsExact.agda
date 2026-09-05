module DASHI.Physics.Accelerators.FlashRadiographyPhysicsExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- GENERIC FLASH-RADIOGRAPHY PHYSICS
------------------------------------------------------------------------

data FlashRadiographyStage : Set where
  pulsedPower
  electronInjection
  inductionAcceleration
  beamTransport
  xRayConversion
  objectTransmission
  detectorResponse
  imageReconstruction
  physicalInference
  : FlashRadiographyStage

record BeamToImageChain : Set where
  constructor beam-to-image-chain
  field
    electronBeam : String
    accelerator : String
    target : String
    photonGeneration : String
    attenuation : String
    detector : String
    reconstruction : String

open BeamToImageChain public

canonicalBeamToImageChain : BeamToImageChain
canonicalBeamToImageChain = beam-to-image-chain
  "high-current relativistic electron pulse with finite emittance, energy spread and spot size"
  "induction cells add accelerating voltage while transport optics confine/focus the beam"
  "high-Z converter intercepts electrons"
  "electron deceleration generates bremsstrahlung X-rays with broad energy spectrum"
  "object density/composition/path length shape transmitted photon fluence"
  "scintillator/imager converts transmitted photons to a calibrated radiographic signal"
  "background correction, geometry calibration, deconvolution and inverse modelling map detector signal to object-state estimates"

record RadiographicResolutionBudget : Set where
  constructor radiographic-resolution-budget
  field
    sourceSpot : String
    motionBlur : String
    detectorBlur : String
    scatter : String
    photonStatistics : String
    geometry : String

open RadiographicResolutionBudget public

canonicalResolutionBudget : RadiographicResolutionBudget
canonicalResolutionBudget = radiographic-resolution-budget
  "finite X-ray source spot sets geometric unsharpness"
  "finite pulse width times object velocity contributes temporal blur"
  "detector point-spread function limits spatial resolution"
  "scattered photons reduce contrast and can bias areal-density estimates"
  "finite photon/electron counts set noise and dynamic-range limits"
  "magnification and source-object-detector distances trade field of view, blur and fluence"

record FlashRadiographyBoundary : Set where
  constructor flash-radiography-boundary
  field
    highBeamEnergyMeansSmallSpot : Bool
    highBeamEnergyMeansSmallSpotIsFalse : highBeamEnergyMeansSmallSpot ≡ false
    highDoseMeansHighResolution : Bool
    highDoseMeansHighResolutionIsFalse : highDoseMeansHighResolution ≡ false
    publicAcceleratorLayoutDeterminesInverseModel : Bool
    publicAcceleratorLayoutDeterminesInverseModelIsFalse : publicAcceleratorLayoutDeterminesInverseModel ≡ false
    radiographDirectlyEqualsDensityField : Bool
    radiographDirectlyEqualsDensityFieldIsFalse : radiographDirectlyEqualsDensityField ≡ false
    sameImageMeansUniqueHydrodynamicState : Bool
    sameImageMeansUniqueHydrodynamicStateIsFalse : sameImageMeansUniqueHydrodynamicState ≡ false

canonicalFlashRadiographyBoundary : FlashRadiographyBoundary
canonicalFlashRadiographyBoundary = flash-radiography-boundary
  false refl
  false refl
  false refl
  false refl
  false refl

data FlashRadiographyReverseTarget : Set where
  needBeamPhaseSpace
  needConverterResponse
  needDetectorCalibration
  needScatterModel
  needGeometryCalibration
  needInverseModel
  needUncertaintyPropagation
  : FlashRadiographyReverseTarget
