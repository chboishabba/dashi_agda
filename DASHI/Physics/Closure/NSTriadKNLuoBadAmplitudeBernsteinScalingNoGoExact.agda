module DASHI.Physics.Closure.NSTriadKNLuoBadAmplitudeBernsteinScalingNoGoExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Authors: Alexey Cheskidov; Roman Shvydkoy.
-- Title: "A Unified Approach to Regularity Problems for the 3D Navier-Stokes
-- and Euler Equations: The Use of Kolmogorov's Dissipation Range".
-- DOI: 10.1007/s00021-014-0167-4.
--
-- Author: Terence Tao.
-- Title: "Why Global Regularity for Navier-Stokes Is Hard".
-- DOI: not assigned; expository essay, 2007.
--
-- DASHI CONTRIBUTION
--
-- F7 cannot be closed by a raw three-dimensional Bernstein estimate.  At
-- frequency scale s, the model squared pointwise amplitude and viscous
-- dissipation scale as
--
--   M_Bernstein = s^3 E,
--   D            = s^2 E.
--
-- For any proposed scale-independent coefficient C, choose s = C + 1 and
-- E = 1.  This module proves the exact gap
--
--   s^3 - C s^2 = s^2.
--
-- Hence the direct amplitude-to-diffusion ratio grows like s.  The bad-lane
-- amplitude budget must exploit additional time localization, intermittency,
-- directional increments, or a dissipation-wavenumber condition; ordinary
-- shell Bernstein is supercritical by one full power.
------------------------------------------------------------------------

open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _+_; _*_; _-_; _≤_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (_≡_)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2

counterScale : ℚ → ℚ
counterScale coefficient = coefficient + 1ℚ

bernsteinAmplitudeSquared : ℚ → ℚ
bernsteinAmplitudeSquared scale = scale * scale * scale

shellDiffusionSquared : ℚ → ℚ
shellDiffusionSquared = L2.square

bernsteinAmplitudeGap : ℚ → ℚ
bernsteinAmplitudeGap coefficient =
  bernsteinAmplitudeSquared (counterScale coefficient)
  - coefficient * shellDiffusionSquared (counterScale coefficient)

bernsteinSupercriticalGapIdentity :
  ∀ coefficient →
  bernsteinAmplitudeGap coefficient
  ≡ shellDiffusionSquared (counterScale coefficient)
bernsteinSupercriticalGapIdentity coefficient =
  solve (coefficient ∷ [])

scaledEnergyBernsteinGapIdentity :
  ∀ coefficient energy →
  bernsteinAmplitudeSquared (counterScale coefficient) * energy
  - coefficient
      * (shellDiffusionSquared (counterScale coefficient) * energy)
  ≡ shellDiffusionSquared (counterScale coefficient) * energy
scaledEnergyBernsteinGapIdentity coefficient energy =
  solve (coefficient ∷ energy ∷ [])

bernsteinGapNonnegative :
  ∀ coefficient →
  0ℚ ≤ bernsteinAmplitudeGap coefficient
bernsteinGapNonnegative coefficient
  rewrite bernsteinSupercriticalGapIdentity coefficient =
  L2.squareNonnegative (counterScale coefficient)

record BernsteinAmplitudeAuthorityBoundary : Set where
  constructor bernsteinAmplitudeAuthorityBoundary
  field
    exactOnePowerScalingGapProved : Set
    rawBernsteinAmplitudeBudgetRejected : Set
    timeLocalizedAmplitudeBudgetProduced : Set
    intermittencyGainProduced : Set
    scaleUniformBadLaneCoefficientProduced : Set

canonicalBernsteinAmplitudeAuthorityBoundary :
  BernsteinAmplitudeAuthorityBoundary
canonicalBernsteinAmplitudeAuthorityBoundary =
  bernsteinAmplitudeAuthorityBoundary ⊤ ⊤ ⊥ ⊥ ⊥
  where
  open import Data.Unit using (⊤)
  open import Data.Empty using (⊥)
