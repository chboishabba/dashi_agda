module DASHI.Physics.YangMills.BalabanP0SU2HaarQuarticFormalJetExact where

-- Exact SU(2) Haar FORMAL EVEN FOURTH-JET coefficient algebra.
-- In the Pauli-half exponential-coordinate convention (r is the
-- norm of the Lie algebra coordinate),
--
--     J(r)=(sin(r/2)/(r/2))^2
--         = 1 - r^2/12 + r^4/360 + O(r^6);
--     log J(r) = -r^2/12 -r^4/1440 + O(r^6).
--
-- The physical effective-action Haar insertion is -log J, hence both
-- selected coefficients are POSITIVE (+1/12, +1/1440).
--
-- These declarations certify the PURE RATIONAL FORMAL JET algebra
-- and the corrected signs. They do NOT construct analytic Taylor
-- remainders, prove original SU(2) Jacobian equality, or identify
-- the selected Bałaban finite-cutoff chart. Those are genuine open
-- source-specific physical welds.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using (ℚ; _+_; _-_; _*_; -_; _/_)
import Data.Rational.Tactic.RingSolver as Ring

haarDensityQuadratic : ℚ
haarDensityQuadratic = - (+ 1 / 12)

haarDensityQuartic : ℚ
haarDensityQuartic = + 1 / 360

haarLogQuadratic : ℚ
haarLogQuadratic = - (+ 1 / 12)

haarLogQuartic : ℚ
haarLogQuartic = - (+ 1 / 1440)

haarEffectiveActionQuadratic : ℚ
haarEffectiveActionQuadratic = - haarLogQuadratic

haarEffectiveActionQuartic : ℚ
haarEffectiveActionQuartic = - haarLogQuartic

-- For a formal series Y = a r^2 + b r^4, exp Y has quartic
-- coefficient b + a^2/2. That matches the ACTUAL Haar density jet.
haarLogExpFourthCoefficientExact :
  haarLogQuartic
    + (haarLogQuadratic * haarLogQuadratic) * (+ 1 / 2)
    ≡ haarDensityQuartic
haarLogExpFourthCoefficientExact = Ring.solve-∀

haarLogExpSecondCoefficientExact :
  haarLogQuadratic ≡ haarDensityQuadratic
haarLogExpSecondCoefficientExact = refl

haarEffectiveActionQuadraticPositiveCoefficient :
  haarEffectiveActionQuadratic ≡ (+ 1 / 12)
haarEffectiveActionQuadraticPositiveCoefficient = refl

haarEffectiveActionQuarticPositiveCoefficient :
  haarEffectiveActionQuartic ≡ (+ 1 / 1440)
haarEffectiveActionQuarticPositiveCoefficient = refl

-- The author's proposed O(r^4/180) can be a loose bound on a
-- sufficiently small interval, but it is NOT established by
-- the equality of the formal r^4 coefficient alone.
