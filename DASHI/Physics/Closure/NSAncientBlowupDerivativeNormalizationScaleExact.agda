module DASHI.Physics.Closure.NSAncientBlowupDerivativeNormalizationScaleExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE / CONTEXT
--
-- Authors: Gabriel Koch; Nikolai Nadirashvili; Gregory A. Seregin;
--          Vladimir Sverak.
-- Title: "Liouville theorems for the Navier-Stokes equations and applications".
-- DOI: 10.1007/s11511-009-0039-6.
--
-- Authors: Zhen Lei; Qi S. Zhang; Na Zhao.
-- Title: "Improved Liouville theorems for axially symmetric Navier-Stokes
--         equations".
-- DOI: 10.1360/N012016-00149.
--
-- PURPOSE
-- Standard velocity-maximum blow-up uses
--
--   u_M(y,s) = M^{-1} u(x0 + y/M, t0 + s/M^2).
--
-- Hence velocity values carry one inverse power of M, whereas one spatial
-- derivative carries two inverse powers.  A derivative-normalized ancient
-- limit therefore needs a new scale-invariant lower bound of size
-- |grad u| / M^2; it is not a consequence of |u| / M = 1 alone.
-- This file proves that exponent seam exactly on the rational scale carrier.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 1ℚ; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; trans)

velocityScale : ℚ → ℚ → ℚ
velocityScale mu U = mu * U

gradientScale : ℚ → ℚ → ℚ
gradientScale mu G = (mu * mu) * G

velocityMaximumNormalizes :
  (mu M : ℚ) →
  mu * M ≡ 1ℚ →
  velocityScale mu M ≡ 1ℚ
velocityMaximumNormalizes mu M inverseScale = inverseScale

derivativeCarriesTwoInverseScalePowers :
  (mu G : ℚ) →
  gradientScale mu G ≡ (mu * mu) * G
derivativeCarriesTwoInverseScalePowers mu G = refl

squareInverseScale :
  (mu M : ℚ) →
  mu * M ≡ 1ℚ →
  (mu * mu) * (M * M) ≡ 1ℚ
squareInverseScale mu M inverseScale =
  trans
    (solve (mu ∷ M ∷ []))
    (cong (λ z → z * z) inverseScale)

quadraticGradientGrowthNormalizesDerivative :
  (mu M G : ℚ) →
  mu * M ≡ 1ℚ →
  G ≡ M * M →
  gradientScale mu G ≡ 1ℚ
quadraticGradientGrowthNormalizesDerivative mu M G inverseScale gradientAtQuadraticScale =
  trans
    (cong ((mu * mu) *_) gradientAtQuadraticScale)
    (squareInverseScale mu M inverseScale)

-- Therefore the missing R1 input can be stated without ambiguity:
-- find a blow-up sequence for which a Galilean-invariant spatial oscillation
-- (or derivative) survives velocity normalization.  Derivative survival is
-- equivalent to controlling a quantity at the M^2 scale, not merely M.
