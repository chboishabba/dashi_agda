module DASHI.Physics.Closure.NSTriadKNPressureHessianFourierIsometryRound81Exact where

------------------------------------------------------------------------
-- ROUND81 / PRESSURE-HESSIAN FOURIER ISOMETRY
--
-- For a nonzero periodic Fourier mode k and mean-zero Poisson source h,
--
--     -Delta p = h,
--
-- the pressure-Hessian multiplier is, up to the harmless common sign,
--
--     H_ij(k) = (k_i k_j / |k|^2) h(k).
--
-- Summing the squared nine Frobenius coordinates gives exactly
--
--   sum_ij |H_ij(k)|^2
--     = [sum_ij k_i^2 k_j^2 / |k|^4] |h(k)|^2
--     = |h(k)|^2,
--
-- because sum_ij k_i^2 k_j^2 = |k|^4.
--
-- This module proves that multiplier identity on the repository's exact
-- rational finite-mode arithmetic.  Together with the already-selected
-- coefficient-unitary Parseval convention, it identifies the natural L2
-- pressure-Hessian currency: the full Frobenius L2 mass is no larger than (and
-- on the complete mean-zero mode set exactly equals) the pressure-source L2
-- mass.  The remaining C4 issue is not an L2 Riesz loss; it is obtaining the
-- right localized/selected-event budget and controlling projection/localization
-- commutators without losing the critical gain.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 1ℚ; _+_; _*_; _≡ᵇ_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; trans)

square : ℚ → ℚ
square x = x * x

record NonzeroModePoissonMultiplier : Set where
  field
    kx ky kz inverseRadiusSquared sourceCoefficient : ℚ

    inverseRadiusSquaredExact :
      (square kx + square ky + square kz) * inverseRadiusSquared ≡ 1ℚ

open NonzeroModePoissonMultiplier public

radiusSquared : NonzeroModePoissonMultiplier → ℚ
radiusSquared datum =
  square (kx datum) + square (ky datum) + square (kz datum)

hessianCoefficient :
  NonzeroModePoissonMultiplier →
  ℚ → ℚ → ℚ
hessianCoefficient datum ki kj =
  ki * kj * inverseRadiusSquared datum * sourceCoefficient datum

hessianFrobeniusSquareEnergy : NonzeroModePoissonMultiplier → ℚ
hessianFrobeniusSquareEnergy datum =
    square (hessianCoefficient datum (kx datum) (kx datum))
  + square (hessianCoefficient datum (kx datum) (ky datum))
  + square (hessianCoefficient datum (kx datum) (kz datum))
  + square (hessianCoefficient datum (ky datum) (kx datum))
  + square (hessianCoefficient datum (ky datum) (ky datum))
  + square (hessianCoefficient datum (ky datum) (kz datum))
  + square (hessianCoefficient datum (kz datum) (kx datum))
  + square (hessianCoefficient datum (kz datum) (ky datum))
  + square (hessianCoefficient datum (kz datum) (kz datum))

hessianFrobeniusFactorsThroughRadius :
  (datum : NonzeroModePoissonMultiplier) →
  hessianFrobeniusSquareEnergy datum
  ≡ square (sourceCoefficient datum)
    * square (radiusSquared datum * inverseRadiusSquared datum)
hessianFrobeniusFactorsThroughRadius datum =
  ℚRing.solve-∀
    (kx datum) (ky datum) (kz datum)
    (inverseRadiusSquared datum) (sourceCoefficient datum)

pressureHessianModeFrobeniusIsometry :
  (datum : NonzeroModePoissonMultiplier) →
  hessianFrobeniusSquareEnergy datum ≡ square (sourceCoefficient datum)
pressureHessianModeFrobeniusIsometry datum =
  trans
    (hessianFrobeniusFactorsThroughRadius datum)
    (trans
      (cong
        (λ unit → square (sourceCoefficient datum) * square unit)
        (inverseRadiusSquaredExact datum))
      (ℚRing.solve-∀ (sourceCoefficient datum)))

round81PressureHessianFourierModeIsometryConstructed : Bool
round81PressureHessianFourierModeIsometryConstructed = true

round81PressureHessianFourierModeIsometryConstructedIsTrue :
  round81PressureHessianFourierModeIsometryConstructed ≡ true
round81PressureHessianFourierModeIsometryConstructedIsTrue = refl
