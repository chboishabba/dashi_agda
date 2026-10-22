module DASHI.Physics.QuantumSensors.NVPhotonBinaryLikelihoodExact where

-- Normalized two-outcome photon-detection likelihood; a finite Bernoulli
-- counting gate, not a calibrated NV fluorescence Poisson model.
-- Probabilities are rational and require positivity witnesses separately.
-- Optical readout is conditional on a resonant spin-state calibration.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)

record BinaryPhotonLikelihood : Set where
  constructor binary-photon
  field
    photon : ℚ
    noPhoton : ℚ
    normalized : photon + noPhoton ≡ 1ℚ
    Nonnegative : ℚ → Set
    photonNonnegative : Nonnegative photon
    noPhotonNonnegative : Nonnegative noPhoton
open BinaryPhotonLikelihood public

-- The construction is conditional on explicit photon and no-photon
-- nonnegativity. This disallows silent probability promotion from p+q=1.
fromPhotonFraction :
  (p : ℚ) (Nonnegative : ℚ → Set) →
  Nonnegative p →
  Nonnegative (1ℚ - p) →
  BinaryPhotonLikelihood
fromPhotonFraction p bound hp hq =
  binary-photon p (1ℚ - p) (solve (p ∷ [])) bound hp hq

-- Variance of the Bernoulli count in the algebraic model.
variance : BinaryPhotonLikelihood → ℚ
variance d = photon d * noPhoton d

expectedSquaredCount : BinaryPhotonLikelihood → ℚ
expectedSquaredCount d = photon d

-- Multi-photon counting and optical shot noise require a separate
-- likelihood model; this is a one-gate binary detector only.
