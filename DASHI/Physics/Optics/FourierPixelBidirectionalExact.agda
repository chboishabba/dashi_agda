module DASHI.Physics.Optics.FourierPixelBidirectionalExact where

-- Original experiment (not authored by DASHI):
-- Y. M. Glauser, S. J. W. Vonk, D. B. Seda, H. Niese, et al.,
-- "Fourier pixels for bidirectional light control", Nature 655, 87-92
-- (2026), DOI 10.1038/s41586-026-10681-7, published 24 June 2026.
-- Earlier preprint: arXiv:2601.09022, 13 January 2026, titled
-- "Fourier pixels for reciprocal light control".
--
-- Repository-local finite abstractions/proof candidates below belong to
-- this implementation, NOT to the original authors. No empirical data or
-- Agda kernel result is asserted by this source file alone.
--
-- Reuse instead of duplication:
--   DASHI.Physics.Optics.DiffuserImagingObserverDynamicRangeExact
--   DASHI.Physics.Optics.FresnelZonePlateDiffuserCodecBridgeExact
--   DASHI.Physics.Optics.MultiscaleApertureSynthesisKernelBridge
--   DASHI.Physics.Optics.OpticalPhenomenaKernelBridge
-- Optical phase is a complex-field quantity; detected photon intensity is
-- not phase and global phase cannot be inferred without a phase reference.

open import Agda.Primitive using (Set; Set₁)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong)

-- A physical receipt must weld the very same fabricated surface and
-- excitation, plus the calibrated intensity readout, to the ideal model.
-- These are proof obligations, NOT instantiated claims about the Nature device.
record SameDeviceFourierPixel
    (Incoming Guided Surface Outgoing RawIntensity Recorded : Set) : Set₁ where
  field
    launch : Incoming → Guided
    outcouple : Surface → Guided → Outgoing
    physicalOutput : Surface → Incoming → Outgoing
    physicalOutputWeld : (h : Surface) (e : Incoming) →
      physicalOutput h e ≡ outcouple h (launch e)
    detectionIntensity : Outgoing → RawIntensity
    digitize : RawIntensity → Recorded
    measured : Surface → Incoming → Recorded
    measuredWeld : (h : Surface) (e : Incoming) →
      measured h e ≡ digitize (detectionIntensity (physicalOutput h e))

-- Ideal inverse propagation: it is a condition on an optical forward
-- operator, not a Maxwell derivation or a numerical fabrication tolerance.
record IdealBackPropagation (Field : Set) : Set₁ where
  field
    forward : Field → Field
    backPropagate : Field → Field
    forwardAfterBack : (goal : Field) →
      forward (backPropagate goal) ≡ goal

-- Four unit-modulus input phases: 0, pi/2, pi, 3pi/2.
-- This is a restricted finite code, NOT arbitrary continuous phase recovery.
data Phase4 : Set where
  phase0 phase90 phase180 phase270 : Phase4

-- All four phases have the same bare intensity |E|^2 = 1.
-- The exact Gaussian-integer arithmetic is executed independently in
-- scripts/check_fourier_pixel_exact.py, using E = 1, i, -1, -i.
bareIntensity : Phase4 → ℕ
bareIntensity _ = 1

phase0Not180 : phase0 ≡ phase180 → ⊥
phase0Not180 ()

bareIntensityCollision :
  bareIntensity phase0 ≡ bareIntensity phase180
bareIntensityCollision = refl

-- No postprocessing, however sophisticated, recovers every phase state
-- from this single bare-intensity observation.
noUniversalBareIntensityPhaseDecoder :
  (decode : ℕ → Phase4) →
  ((p : Phase4) → decode (bareIntensity p) ≡ p) → ⊥
noUniversalBareIntensityPhaseDecoder decode correct =
  phase0Not180
    (trans (sym (correct phase0))
      (trans (cong decode bareIntensityCollision)
        (correct phase180)))

-- Two phase-diverse, coherently interferometric, ideal calibrated readings:
-- x = |E+1|^2, y = |E+i|^2.
-- Unit incoming magnitude and exact, stable reference phases are assumed.
-- Numerical values are exact and cross-checked by the Python fixture.
record QuadratureReadout : Set where
  constructor quad
  field
    xIntensity : ℕ
    yIntensity : ℕ

quadratures : Phase4 → QuadratureReadout
quadratures phase0   = quad 4 2
quadratures phase90  = quad 2 4
quadratures phase180 = quad 0 2
quadratures phase270 = quad 2 0

-- In contrast to the bare-intensity observation, both quadratures identify
-- every element of THIS restricted four-state carrier.
quadraturesInjective :
  (p q : Phase4) → quadratures p ≡ quadratures q → p ≡ q
quadraturesInjective phase0   phase0   eq = refl
quadraturesInjective phase0   phase90  ()
quadraturesInjective phase0   phase180 ()
quadraturesInjective phase0   phase270 ()
quadraturesInjective phase90  phase0   ()
quadraturesInjective phase90  phase90  eq = refl
quadraturesInjective phase90  phase180 ()
quadraturesInjective phase90  phase270 ()
quadraturesInjective phase180 phase0   ()
quadraturesInjective phase180 phase90  ()
quadraturesInjective phase180 phase180 eq = refl
quadraturesInjective phase180 phase270 ()
quadraturesInjective phase270 phase0   ()
quadraturesInjective phase270 phase90  ()
quadraturesInjective phase270 phase180 ()
quadraturesInjective phase270 phase270 eq = refl

-- One of the two interferometric readings alone still loses information.
xOnly : Phase4 → ℕ
xOnly p = QuadratureReadout.xIntensity (quadratures p)

xOnlyCollision : xOnly phase90 ≡ xOnly phase270
xOnlyCollision = refl

phase90Not270 : phase90 ≡ phase270 → ⊥
phase90Not270 ()

noUniversalOneQuadratureDecoder :
  (decode : ℕ → Phase4) →
  ((p : Phase4) → decode (xOnly p) ≡ p) → ⊥
noUniversalOneQuadratureDecoder decode correct =
  phase90Not270
    (trans (sym (correct phase90))
      (trans (cong decode xOnlyCollision)
        (correct phase270)))

-- Neither theorem asserts all-scene injectivity, stability under photon
-- noise, Stokes recovery in arbitrary illumination, or fabrication fidelity.
-- A reconfigurable display additionally needs a dynamic *on-device* control
-- path, material response, bandwidth/power/lifetime receipts and array wiring.
