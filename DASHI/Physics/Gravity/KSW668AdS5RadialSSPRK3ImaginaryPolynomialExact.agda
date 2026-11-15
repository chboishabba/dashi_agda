module DASHI.Physics.Gravity.KSW668AdS5RadialSSPRK3ImaginaryPolynomialExact where

------------------------------------------------------------------------
-- Original moving AdS5 F8 effective d=3,7,11 radial finite-volume
-- pure-wave stability factor, NOT the coupled moving y,r PDE proof.
--
-- SSPRK3 polynomial P(z)=1+z+z²/2+z³/6.
-- For z=i*x, real=1-x²/2 and imag=x-x³/6.
-- Prove over arbitrary rational x:
--   |P(i*x)|² = 1 + x^4*(x²-3)/36.
--
-- This is the EXACT rational identity behind the radial modal
-- stability interval |x|<=sqrt(3). The real-ordered spectral
-- estimate, Neumann wall SAT coupling, continuum Weyl trace and
-- Agda 2.9 kernel acceptance remain separately OPEN.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base using (ℚ; 1ℚ; _+_; _*_; -_; _/_)
open import Data.Rational.Tactic.RingSolver using (solve)

half sixth thirtySixth three : ℚ
half = (+ 1) / 2
sixth = (+ 1) / 6
thirtySixth = (+ 1) / 36
three = (+ 3) / 1

fourthPower : ℚ → ℚ
fourthPower x = (x * x) * (x * x)

realPartSSPRK3I : ℚ → ℚ
realPartSSPRK3I x = 1ℚ + - (half * (x * x))

imagPartSSPRK3I : ℚ → ℚ
imagPartSSPRK3I x =
  x + - (sixth * (x * x * x))

originalRadialImaginaryAmplificationExact : (x : ℚ) →
  realPartSSPRK3I x * realPartSSPRK3I x
    + imagPartSSPRK3I x * imagPartSSPRK3I x
  ≡ 1ℚ
    + thirtySixth * fourthPower x * (x * x + - three)
originalRadialImaginaryAmplificationExact x = solve []
