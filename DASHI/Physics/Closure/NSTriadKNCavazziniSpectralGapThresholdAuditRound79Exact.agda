module DASHI.Physics.Closure.NSTriadKNCavazziniSpectralGapThresholdAuditRound79Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCE / CONTEXT
--
-- Author: Andrea Cavazzini.
-- Title: "Self-Frustration of Vortex Stretching and the Architecture of the
-- Navier-Stokes Blow-Up Barrier".
-- Zenodo preprint (2026).
-- DOI: 10.5281/zenodo.19158797.
--
-- ROUND79 / USEFUL ALGEBRA SEPARATED FROM UNSAFE DENOMINATOR PROMOTION
--
-- The source's effective alignment-rate threshold is algebraically
--
--   4 gbar g12 > M^2.
--
-- In the restricted case gbar=g12 this becomes
--
--   4 g^2 > M^2,
--
-- and the polynomial difference factors exactly as
--
--   4 g^2 - M^2 = (2g-M)(2g+M).
--
-- That threshold algebra is useful and is retained here. It does NOT provide
-- the separate lower bound g_j3 >= c M required to divide an off-diagonal
-- pressure-Hessian numerator by a physical strain gap. Round79's periodic
-- pure-rotation counterexample explicitly blocks deriving such a lower bound
-- from incompressibility/trace-free ordering alone.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; _/_; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)

four two : ℚ
four = Int.+ 4 / 1
two = Int.+ 2 / 1

spectralThresholdPolynomial : ℚ → ℚ → ℚ → ℚ
spectralThresholdPolynomial gbar g12 M =
  (four * gbar * g12) - (M * M)

restrictedThresholdPolynomial : ℚ → ℚ → ℚ
restrictedThresholdPolynomial g M =
  (four * g * g) - (M * M)

restrictedThresholdFactors : ∀ g M →
  restrictedThresholdPolynomial g M
  ≡ ((two * g) - M) * ((two * g) + M)
restrictedThresholdFactors g M = solve (g ∷ M ∷ [])

round79CavazziniSpectralThresholdAlgebraRetained : Bool
round79CavazziniSpectralThresholdAlgebraRetained = true

round79CavazziniGapComparableToVorticityImportedAsAuthority : Bool
round79CavazziniGapComparableToVorticityImportedAsAuthority = false

round79CavazziniGapComparableToVorticityImportedAsAuthorityIsFalse :
  round79CavazziniGapComparableToVorticityImportedAsAuthority ≡ false
round79CavazziniGapComparableToVorticityImportedAsAuthorityIsFalse = refl
