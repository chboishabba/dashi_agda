module DASHI.Physics.Optics.FresnelZonePlateDiffuserCodecBridgeExact where

-- SOURCE / CLAIM BOUNDARY
--
-- This module is a mathematical bridge between diffuser lensless cameras,
-- Fresnel zone plate (FZP) coded-aperture cameras, and their recorded
-- sensor observations. It does NOT claim an optical propagation derivation.
--
-- External literature:
--   doi:10.1038/s41377-020-0289-9   single-shot FZA with incoherent light
--   doi:10.1364/OL.497086           FZP single-shot confocal imaging
--   doi:10.1016/j.optlaseng.2026.109762  FZA finite-sampling issue
--
-- Optical holography: coherent field interference and reference waves
-- differ from incoherent *intensity* addition. A zone-plate pattern can be
-- an analytically designed coding mask, but this does not turn an incoherent
-- measurement into a phase-resolved hologram. The repository's entropy-style
-- holographic area law is a separate subject.

open import Agda.Primitive using (Set; Set₁)
open import Data.Nat using (ℕ; zero; suc; _+_; _⊓_)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong)

import DASHI.Physics.Optics.DiffuserImagingObserverDynamicRangeExact as Camera
import DASHI.Physics.Optics.CatastropheDiffractionNormalFormExact as Diffraction
import DASHI.Physics.Optics.OpticalPhenomenaKernelBridge as Optics
import DASHI.Foundations.HyperformObserverFactorisationExact as Observer

-- Mask families are classifications, not calibrated propagation operators.
data CodedOpticalMask : Set where
  randomDiffuser : CodedOpticalMask
  binaryAmplitudeZonePlate : CodedOpticalMask
  phaseZonePlate : CodedOpticalMask
  continuousGaborZonePlate : CodedOpticalMask

-- For a conventional binary Fresnel zone plate one idealised design
-- uses concentric zone boundaries r_n² = n λ f (paraxial approximation).
-- Numerical aperture, incident field and wavelength determine whether
-- this idealised mask matches a physical instrument.
record ZonePlatePhysicalReceipt
    (Wavelength RadiusSquared FocalScale Field Pattern : Set) : Set₁ where
  field
    maskType : CodedOpticalMask
    wavelength : Wavelength
    focus : FocalScale
    zoneRadiusSquared : ℕ → RadiusSquared
    inputField : Field
    propagatedField : Field
    opticalForward : Field → Field
    propagationMatches : propagatedField ≡ opticalForward inputField
    recordedIntensity : Field → Pattern
    observedPattern : Pattern
    intensityMatches : observedPattern ≡ recordedIntensity propagatedField
    -- Numeric Fresnel/paraxial geometry is an external physical obligation.
    -- This record explicitly does not assert r_n²=n λ f for arbitrary scalars.

-- The camera's linear superposition law is a law of *incoherent intensities*.
-- Amplitudes may interfere before squaring. No mixing of those two carriers.
record IlluminationRegime
    (Field Intensity : Set) : Set₁ where
  field
    fieldToIntensity : Field → Intensity
    fieldSuperposition : Field → Field → Field
    intensityMix : Intensity → Intensity → Intensity
    interferenceResidual :
      Field → Field → Intensity
    -- Evidence that coherent interference is modeled by a distinct term
    -- must be supplied by each concrete numeric model.

-- Distinct signatures alone do not establish full-scene injectivity:
-- a simple finite scene pair can still collapse under a single detector.
data DepthCode : Set where
  near far : DepthCode

depthCodeDistinct : near ≡ far → ⊥
depthCodeDistinct ()

data OneHotScene : Set where
  sourceNear sourceFar : OneHotScene

depthOf : OneHotScene → DepthCode
depthOf sourceNear = near
depthOf sourceFar = far

-- Differing near/far *labels* are not a proof that the observer resolves them.
-- Here the sensor's one-bit clip is identical on both scene alternatives.
intensityOf : OneHotScene → ℕ
intensityOf sourceNear = suc zero
intensityOf sourceFar = suc (suc zero)

saturatedZoneCode : OneHotScene → ℕ
saturatedZoneCode x = Camera.clipAtOne (intensityOf x)

depthSensorCollision :
  saturatedZoneCode sourceNear ≡ saturatedZoneCode sourceFar
depthSensorCollision = refl

noUniversalDepthDecoder :
  (recover : ℕ → DepthCode) →
  ((x : OneHotScene) →
    recover (saturatedZoneCode x) ≡ depthOf x) →
  ⊥
noUniversalDepthDecoder recover correct =
  depthCodeDistinct
    (trans (sym (correct sourceNear))
      (trans (cong recover depthSensorCollision)
        (correct sourceFar)))

-- A *specific* depth-selective observation may be invertible on the
-- restricted two-state class. We can prove this constructively, without
-- claiming an actual calibrated FZP instrument has such a detector.
data TwoPixelCode : Set where
  nearPattern farPattern : TwoPixelCode

encodeDepth : DepthCode → TwoPixelCode
encodeDepth near = nearPattern
encodeDepth far = farPattern

decodeDepth : TwoPixelCode → DepthCode
decodeDepth nearPattern = near
decodeDepth farPattern = far

codedDepthRoundTrip : (z : DepthCode) →
  decodeDepth (encodeDepth z) ≡ z
codedDepthRoundTrip near = refl
codedDepthRoundTrip far = refl

-- Postprocessing a recorded, saturated observation cannot recover depth.
noRechartRepairsSaturatedDepth :
  ∀ {Output : Set} (post : ℕ → Output) →
  post (saturatedZoneCode sourceNear) ≡
  post (saturatedZoneCode sourceFar)
noRechartRepairsSaturatedDepth post =
  cong post depthSensorCollision

-- Physical acceptance criteria, not fulfilled by the finite examples.
record PhysicalZonePlateImager
    (Scene Field Intensity PixelData Pattern Depth : Set) : Set₁ where
  field
    mask : CodedOpticalMask
    propagated : Scene → Field
    photonIntensity : Field → Intensity
    pixelResponse : Intensity → PixelData
    measure : Scene → PixelData
    measurementWeld :
      (x : Scene) →
      measure x ≡ pixelResponse (photonIntensity (propagated x))
    depthSignature : Depth → Pattern
    -- Quantitative wavelength / thickness / sampling / calibration,
    -- shot noise, sensor clipping and stability remain independent.
