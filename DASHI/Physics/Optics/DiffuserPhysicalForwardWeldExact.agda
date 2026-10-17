module DASHI.Physics.Optics.DiffuserPhysicalForwardWeldExact where

-- Same-object weld from a wave-propagation producer to the already-existing
-- diffuser camera encoder.  This module does not introduce a second camera H:
-- every physical prediction must be identified pointwise with the existing
-- DiffuserForwardModel.encode and its existing depth-indexed PSF family.

open import Agda.Primitive using (Set; Set₁)
open import Relation.Binary.PropositionalEquality using (_≡_)

import DASHI.Physics.Optics.DiffuserImagingObserverDynamicRangeExact as Camera
import DASHI.Physics.Optics.FresnelAngularSpectrumPropagationExact as Propagation

record PhysicalDiffuserForwardWeld
    {Scene Sensor Position Depth Pattern Field Intensity : Set}
    (M : Camera.DiffuserForwardModel
      Scene Sensor Position Depth Pattern) : Set₁ where
  field
    propagation : Depth → Field → Field
    fieldToIntensity : Field → Intensity
    intensityToSensor : Intensity → Sensor

    physicalEncode : Scene → Sensor
    physicalDepthField : Depth → Field
    physicalDepthPSF : Depth → Pattern

    -- This is the critical same-object payment: physical optics lands on the
    -- exact camera encoder already consumed by reconstruction/stability code.
    encodeIsPhysicalIntensity :
      (x : Scene) → Camera.encode M x ≡ physicalEncode x

    depthPSFIsPhysical :
      (z : Depth) → Camera.atDepth M z ≡ physicalDepthPSF z

    depthFieldToSensor :
      (z : Depth) →
      Camera.patternToSensor M (physicalDepthPSF z) ≡
      intensityToSensor (fieldToIntensity (physicalDepthField z))

    -- Physical calibration remains an independently supplied receipt.
    calibrationAuthority : Set
    calibrationReceipt : calibrationAuthority

open PhysicalDiffuserForwardWeld public

record PropagationBackedDepthPSF
    {Geometry Wavelength Distance Field Pattern : Set}
    (F : Propagation.FresnelPropagationReceipt
      Geometry Wavelength Distance Field) : Set₁ where
  field
    fieldToPattern : Field → Pattern
    selectedPattern : Pattern
    selectedPatternWeld :
      selectedPattern ≡ fieldToPattern (Propagation.propagatedField F)

open PropagationBackedDepthPSF public
