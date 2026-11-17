module DASHI.Physics.Gravity.KSW668F8RationalAxialTTCubatureExact where

------------------------------------------------------------------------
-- Maximum-cut XXXIV: 12-point RATIONAL angular projection for the
-- ORIGINAL fourth-order full tensor TT Fourier symbol.
--
-- Cardinal nodes: (+/-1,0),(0,+/-1), weight 527/4608 each.
-- Diagonal nodes: (+/-3/5,+/-4/5), (+/-4/5,+/-3/5),
--                weight 625/9216 each.
-- Exact on all polynomials in (y,z) of total degree <=4, the original
-- tensor symbol's full angular degree. In the x-axis Fourier receiver
-- kernel exp(i*kx*R), the azimuthal factor is constant, so this
-- projection isolates the original T_yy m=0 axisymmetric multiplier.
-- Off-axis exponential Fourier kernels are NOT quartic polynomials.
--
-- These are finite rational identities; a proof equating this
-- cubature with an analytic circle integral for arbitrary fields,
-- the original radial FV commuting diagram, and pinned Agda
-- kernel acceptance remain OPEN. Attribution: original KSW TT owners.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base using (ℚ; 1ℚ; _+_; _*_; -_; _/_)
open import Data.Rational.Tactic.RingSolver using (solve)
import DASHI.Physics.Gravity.KSW668F8TTSymbolDiscreteCompatibilityExact as TT

q0 q1 q3 q4 q5 : ℚ
q0 = (+ 0) / 1
q1 = (+ 1) / 1
q3 = (+ 3) / 5
q4 = (+ 4) / 5
q5 = (+ 527) / 4608

cardinal4 : (ℚ → ℚ → ℚ) → ℚ
cardinal4 f =
  f q1 q0 + f (- q1) q0
    + f q0 q1 + f q0 (- q1)

diagonal8 : (ℚ → ℚ → ℚ) → ℚ
diagonal8 f =
  f q3 q4 + f q3 (- q4) + f (- q3) q4 + f (- q3) (- q4)
  + f q4 q3 + f q4 (- q3) + f (- q4) q3 + f (- q4) (- q3)

rationalAzimuthalMean : (ℚ → ℚ → ℚ) → ℚ
rationalAzimuthalMean f =
  q5 * cardinal4 f + ((+ 625) / 9216) * diagonal8 f

cardinalMean : (ℚ → ℚ → ℚ) → ℚ
cardinalMean f = ((+ 1) / 4) * cardinal4 f

-- Moment basis for the angular polynomial space through degree four.
cubatureMass :
  rationalAzimuthalMean (λ y z → q1) ≡ q1
cubatureMass = solve []

cubatureYMean :
  rationalAzimuthalMean (λ y z → y) ≡ q0
cubatureYMean = solve []

cubatureYZMean :
  rationalAzimuthalMean (λ y z → y * z) ≡ q0
cubatureYZMean = solve []

cubatureY2 :
  rationalAzimuthalMean (λ y z → y * y) ≡ ((+ 1) / 2)
cubatureY2 = solve []

cubatureY4 :
  rationalAzimuthalMean (λ y z → y * y * y * y)
    ≡ ((+ 3) / 8)
cubatureY4 = solve []

cubatureY2Z2 :
  rationalAzimuthalMean (λ y z → y * y * z * z)
    ≡ ((+ 1) / 8)
cubatureY2Z2 = solve []

cubatureZ4 :
  rationalAzimuthalMean (λ y z → z * z * z * z)
    ≡ ((+ 3) / 8)
cubatureZ4 = solve []

axisA0 : ℚ → ℚ → ℚ
axisA0 x rho =
  ((+ 1) / 8) *
    ((x * x + rho * rho) * (x * x + rho * rho)
      + ((+ 6) / 1) * (x * x + rho * rho) * x * x
      + x * x * x * x)

-- Exact projection of the FULL original TT tensor, not just a yy
-- component substitution. At fixed longitudinal x, transverse rho.
axisAverageXX :
  (x rho : ℚ) →
  rationalAzimuthalMean (λ y z → TT.ttXX x (rho * y) (rho * z))
    ≡ q0
axisAverageXX x rho = solve []

axisAverageXY :
  (x rho : ℚ) →
  rationalAzimuthalMean (λ y z → TT.ttXY x (rho * y) (rho * z))
    ≡ q0
axisAverageXY x rho = solve []

axisAverageXZ :
  (x rho : ℚ) →
  rationalAzimuthalMean (λ y z → TT.ttXZ x (rho * y) (rho * z))
    ≡ q0
axisAverageXZ x rho = solve []

axisAverageYY :
  (x rho : ℚ) →
  rationalAzimuthalMean (λ y z → TT.ttYY x (rho * y) (rho * z))
    ≡ axisA0 x rho
axisAverageYY x rho = solve []

axisAverageYZ :
  (x rho : ℚ) →
  rationalAzimuthalMean (λ y z → TT.ttYZ x (rho * y) (rho * z))
    ≡ q0
axisAverageYZ x rho = solve []

axisAverageZZ :
  (x rho : ℚ) →
  rationalAzimuthalMean (λ y z → TT.ttZZ x (rho * y) (rho * z))
    ≡ - (axisA0 x rho)
axisAverageZZ x rho = solve []

-- Negative control: a four-cardinal-point angular discretization
-- aliases the original m=4 yy mode to a spurious rho^4/8.
fourCardinalTTYYAlias :
  (x rho : ℚ) →
  cardinalMean (λ y z → TT.ttYY x (rho * y) (rho * z))
    ≡ axisA0 x rho + ((+ 1) / 8) * rho * rho * rho * rho
fourCardinalTTYYAlias x rho = solve []
