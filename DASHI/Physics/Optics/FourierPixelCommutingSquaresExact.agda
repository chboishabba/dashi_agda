module DASHI.Physics.Optics.FourierPixelCommutingSquaresExact where

------------------------------------------------------------------------
-- ATTRIBUTION AND AUTHORITY
-- Original physical experiment: Glauser, Vonk, Seda et al.,
-- Nature 655 (2026), 87-92, DOI 10.1038/s41586-026-10681-7.
-- This is new source-written DASHI mathematical reconstruction, NOT a
-- source-authored theorem and NOT proof of a measured device's transfer map.
--
-- Reuse EXACT pre-existing generic theorem owners:
-- DASHI.Physics.Limits.PhysicsLimitCommutingSquare
-- DASHI.Core.ReopenableConsumerInterventionKernelExact
-- DASHI.Physics.Optics.DiffuserImagingObserverDynamicRangeExact
--
-- Every exact square below is either (i) a CONDITIONAL physical bridge
-- whose correctness field is an explicit remaining obligation, or
-- (ii) a CONCRETE four-phase finite mathematical witness.
------------------------------------------------------------------------

open import Agda.Primitive using (Set; Set₁)
open import Data.Nat using (ℕ)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong)

import DASHI.Physics.Limits.PhysicsLimitCommutingSquare as Sq
import DASHI.Core.ReopenableConsumerInterventionKernelExact as Core
import DASHI.Physics.Optics.FourierPixelBidirectionalExact as Pixel
import DASHI.Physics.Optics.DiffuserImagingObserverDynamicRangeExact as Camera

------------------------------------------------------------------------
-- 1. SAME DEVICE: optical generation and detection really follow
-- different paths, but they terminate at the same recorded reading
-- ONLY when the device's calibration weld is supplied.
------------------------------------------------------------------------

physicalMeasurementSquare :
  {Input Guided Surface Output Intensity Recorded : Set} →
  (device : Pixel.SameDeviceFourierPixel
    Input Guided Surface Output Intensity Recorded) →
  (surface : Surface) →
  Sq.CommutingSquare Input Output Input Recorded
physicalMeasurementSquare device surface = record
  { top = Pixel.SameDeviceFourierPixel.physicalOutput device surface
  ; left = λ e → e
  ; right = λ o →
      Pixel.SameDeviceFourierPixel.digitize device
        (Pixel.SameDeviceFourierPixel.detectionIntensity device o)
  ; bottom = Pixel.SameDeviceFourierPixel.measured device surface
  }

physicalMeasurementExact :
  {Input Guided Surface Output Intensity Recorded : Set} →
  (device : Pixel.SameDeviceFourierPixel
    Input Guided Surface Output Intensity Recorded) →
  (surface : Surface) →
  Sq.ExactCommutation (physicalMeasurementSquare device surface)
physicalMeasurementExact device surface = record
  { pathsAgree = λ e →
      sym (Pixel.SameDeviceFourierPixel.measuredWeld device surface e)
  }

-- Re-export the SAME witnessed law to the repo's generic consumer/
-- intervention operator without duplicating its Intertwiner calculus.
physicalMeasurementIntertwiner :
  {Input Guided Surface Output Intensity Recorded : Set} →
  (device : Pixel.SameDeviceFourierPixel
    Input Guided Surface Output Intensity Recorded) →
  (surface : Surface) →
  Core.Intertwiner
    (λ e → e)
    (λ o →
      Pixel.SameDeviceFourierPixel.digitize device
        (Pixel.SameDeviceFourierPixel.detectionIntensity device o))
    (Pixel.SameDeviceFourierPixel.physicalOutput device surface)
    (Pixel.SameDeviceFourierPixel.measured device surface)
physicalMeasurementIntertwiner device surface =
  Core.intertwiner λ e →
    Sq.pathIndependence (physicalMeasurementExact device surface) e

------------------------------------------------------------------------
-- 2. INVERSE-DESIGN SQUARE: specification -> physical output.
-- The guarantee is not created by the record; a SAME-surface correction
-- receipt must be independently measured/proved for a selected device.
------------------------------------------------------------------------

record SameDeviceDesignContract
    {Goal Input Guided Surface Output Intensity Recorded : Set}
    (device : Pixel.SameDeviceFourierPixel
      Input Guided Surface Output Intensity Recorded)
    (excitation : Input) : Set₁ where
  field
    makeSurface : Goal → Surface
    targetField : Goal → Output
    designCorrect : (goal : Goal) →
      Pixel.SameDeviceFourierPixel.physicalOutput
        device (makeSurface goal) excitation ≡ targetField goal

open SameDeviceDesignContract public

designExecutionSquare :
  {Goal Input Guided Surface Output Intensity Recorded : Set} →
  {device : Pixel.SameDeviceFourierPixel
    Input Guided Surface Output Intensity Recorded} →
  {excitation : Input} →
  (contract : SameDeviceDesignContract device excitation) →
  Sq.CommutingSquare Goal Surface Goal Output
designExecutionSquare {device = device} {excitation = excitation}
    contract = record
  { top = makeSurface contract
  ; left = λ goal → goal
  ; right = λ surface →
      Pixel.SameDeviceFourierPixel.physicalOutput
        device surface excitation
  ; bottom = targetField contract
  }

designExecutionExact :
  {Goal Input Guided Surface Output Intensity Recorded : Set} →
  {device : Pixel.SameDeviceFourierPixel
    Input Guided Surface Output Intensity Recorded} →
  {excitation : Input} →
  (contract : SameDeviceDesignContract device excitation) →
  Sq.ExactCommutation (designExecutionSquare contract)
designExecutionExact contract =
  record { pathsAgree = designCorrect contract }

------------------------------------------------------------------------
-- 3. RESTRICTED FINITE PHASE QUADRATURES.
-- Classical coherent references, no assertion of single-photon coherence,
-- optical quantum advantage, or a continuously invertible detector.
------------------------------------------------------------------------

open Pixel using
  (Phase4; phase0; phase90; phase180; phase270;
   QuadratureReadout; quad; xIntensity; yIntensity;
   quadratures; bareIntensity; bareIntensityCollision)

-- The catch-all choice has NO significance for readings outside the four
-- admitted codewords. Proving restricted round-trip is the operative law.
decodeFourPhase : QuadratureReadout → Phase4
decodeFourPhase (quad 4 2) = phase0
decodeFourPhase (quad 2 4) = phase90
decodeFourPhase (quad 0 2) = phase180
decodeFourPhase (quad 2 0) = phase270
decodeFourPhase _ = phase0

fourPhaseRoundTrip : (p : Phase4) →
  decodeFourPhase (quadratures p) ≡ p
fourPhaseRoundTrip phase0 = refl
fourPhaseRoundTrip phase90 = refl
fourPhaseRoundTrip phase180 = refl
fourPhaseRoundTrip phase270 = refl

phaseReconstructionSquare :
  Sq.CommutingSquare Phase4 QuadratureReadout Phase4 Phase4
phaseReconstructionSquare = record
  { top = quadratures
  ; left = λ p → p
  ; right = decodeFourPhase
  ; bottom = λ p → p
  }

phaseReconstructionExact :
  Sq.ExactCommutation phaseReconstructionSquare
phaseReconstructionExact =
  record { pathsAgree = fourPhaseRoundTrip }

------------------------------------------------------------------------
-- 4. FORMAL NO-GO USING THE EXISTING CONSUMER-DESCENT THEOREM.
-- A phase-sensitive observer cannot factor through bare intensity even
-- though both mathematical readouts are on the SAME finite input states.
------------------------------------------------------------------------

quad0DifferentFromQuad180 :
  quadratures phase0 ≡ quadratures phase180 → ⊥
quad0DifferentFromQuad180 ()

quadratureIntensityDescentDefect :
  Core.ConsumerDescentDefect bareIntensity quadratures
quadratureIntensityDescentDefect =
  Core.consumerDescentDefect
    phase0 phase180 bareIntensityCollision
    quad0DifferentFromQuad180

noFullQuadratureFromBareIntensity :
  Core.ConsumerDescent bareIntensity quadratures → ⊥
noFullQuadratureFromBareIntensity descent =
  Core.consumerDescentDefectContradictsDescent
    descent quadratureIntensityDescentDefect

-- Explicit failure of the tempting 'coarse forward sensor' square:
-- there is NO map from bare intensity to phase-sensitive x readout that
-- can reproduce the four-state physically coherent measurement.
fourNotZero : 4 ≡ 0 → ⊥
fourNotZero ()

noIntensityToInterferenceSquare :
  (coarseSensor : ℕ → ℕ) →
  Core.Intertwiner
    bareIntensity xIntensity quadratures coarseSensor → ⊥
noIntensityToInterferenceSquare coarseSensor square =
  fourNotZero
    (trans
      (Core.commutes square phase0)
      (sym (Core.commutes square phase180)))

------------------------------------------------------------------------
-- 5. DETECTOR DYNAMIC-RANGE NO-GO. The older camera owner supplies
-- clipAtOne; we do not create another saturation model.
------------------------------------------------------------------------

clippedQuadratures : Phase4 → QuadratureReadout
clippedQuadratures p =
  quad (Camera.clipAtOne (xIntensity (quadratures p)))
       (Camera.clipAtOne (yIntensity (quadratures p)))

clippedQuadraturesCollision :
  clippedQuadratures phase0 ≡ clippedQuadratures phase90
clippedQuadraturesCollision = refl

phase0Not90 : phase0 ≡ phase90 → ⊥
phase0Not90 ()

noDecoderAfterQuadratureClipping :
  (decode : QuadratureReadout → Phase4) →
  ((p : Phase4) → decode (clippedQuadratures p) ≡ p) → ⊥
noDecoderAfterQuadratureClipping decode correct =
  phase0Not90
    (trans
      (sym (correct phase0))
      (trans
        (cong decode clippedQuadraturesCollision)
        (correct phase90)))

-- Successful zero-noise round trips do not remove the need for a
-- quantitative metric, same-device calibration, photon and read noise,
-- finite aperture, optical loss, crosstalk, and dynamical control model.
-- Such quantitative obligations are deliberately NOT defined as exact here.
