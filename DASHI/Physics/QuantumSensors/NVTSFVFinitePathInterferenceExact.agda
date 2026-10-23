module DASHI.Physics.QuantumSensors.NVTSFVFinitePathInterferenceExact where

-- Finite complex-amplitude history sum in rational Gaussian coordinates.
-- This is a *finite toy realization* of interference, not a continuum
-- Feynman measure, calibrated S/hbar, or an NV photon response.
-- Reuses the conceptual phase/admissibility/observation distinctions in
-- ActionPhaseLiftBoundaryExact, TSFVActionPhaseWeightSeparationExact,
-- TSFVBidirectionalCausticBridgeExact and stationary classification.
-- Classical quantum-mechanical amplitudes are prior art (Feynman).

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Agda.Builtin.List using ([]; _∷_)

record GaussianAmplitude : Set where
  constructor amp
  field
    re im : ℚ
open GaussianAmplitude public

_⊞_ : GaussianAmplitude → GaussianAmplitude → GaussianAmplitude
amp a b ⊞ amp c d = amp (a + c) (b + d)

normSquared : GaussianAmplitude → ℚ
normSquared (amp a b) = a * a + b * b

phaseZero phasePi : GaussianAmplitude
phaseZero = amp 1ℚ 0ℚ
phasePi = amp (0ℚ - 1ℚ) 0ℚ

data TwoPath : Set where
  upper lower : TwoPath

pathAmplitude : TwoPath → GaussianAmplitude
pathAmplitude upper = phaseZero
pathAmplitude lower = phasePi

coherentTwoPathSum : GaussianAmplitude
coherentTwoPathSum = pathAmplitude upper ⊞ pathAmplitude lower

incoherentTwoPathIntensity : ℚ
incoherentTwoPathIntensity =
  normSquared (pathAmplitude upper) +
  normSquared (pathAmplitude lower)

coherentCancellation : coherentTwoPathSum ≡ amp 0ℚ 0ℚ
coherentCancellation = refl

coherentIntensityVanishes : normSquared coherentTwoPathSum ≡ 0ℚ
coherentIntensityVanishes = refl

incoherentIntensityTwo : incoherentTwoPathIntensity ≡ 1ℚ + 1ℚ
incoherentIntensityTwo = refl

-- Finite optical detector intensity is a function of the *sum* of
-- amplitudes for histories rendered indistinguishable. The incoherent
-- mixture sums squared magnitudes instead; replacing one by the other
-- erases interference. Neither is a probability without normalization.

-- Explicit history labels are retained even where observations coincide.
-- TSFV must separately produce calibrated amplitudes; this file does
-- not identify Candidate256 mismatch with physical action.
