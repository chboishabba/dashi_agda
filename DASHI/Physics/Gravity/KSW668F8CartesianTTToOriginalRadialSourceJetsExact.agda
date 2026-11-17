module DASHI.Physics.Gravity.KSW668F8CartesianTTToOriginalRadialSourceJetsExact where

------------------------------------------------------------------------
-- XXXVI: ORIGINAL fourth-order Cartesian TT differential generator
-- projected to the ACTUAL F8 radial source profiles G_ell.
--
-- Reuse KSW668F8TTSymbolDiscreteCompatibilityExact and
-- KSW668AdS5TTMultipoleAngularRationalExact; do not rebuild T=PQP...
--
-- Let D=(1/r) d/dr and f a smooth radial scalar on r>0.
-- Cartesian 4-derivative chain rule and transverse azimuthal average
-- give for the original yy component:
--
--   <T_yy(partial)f>_phi
--     = 6 D² f + (2+6 mu²) r² D³ f
--       + [(mu^4+6mu²+1)/8] r^4 D⁴ f .
--
-- The factor 2+6mu² = 4P0+4P2, while the final quartic
-- angular factor = (2/5)P0+(4/7)P2+(1/35)P4.
-- Therefore the original radial profiles are exactly:
--  S0 = 6 D²f +4r²D³f+(2/5)r^4 D⁴f
--  S2 = 4r²D³f+(4/7)r^4 D⁴f
--  S4 = (1/35)r^4 D⁴f.
--
-- To avoid r^-1 or r^-4 at the origin, prove the polynomial
-- r^4-weighted jet algebra for arbitrary rational r,f1..f4:
--  J2=r^4 D²f = r²f2-rf1
--  J3=r^6 D³f = r³f3-3r²f2+3rf1
--  J4=r^8 D⁴f = r^4f4-6r³f3+15r²f2-15rf1.
--
-- This is an exact finite algebra witness matching the ORIGINAL
-- scripts/ksw668_f8_tt_multipole.py profiles. Its use as a
-- smooth-function chain rule, azimuthal integral, tensor-to-FV
-- commuting diagram or Agda continuum derivative theorem still
-- requires analytic witnesses. Pinned Agda kernel NOT RUN.
-- Original DASHI / Caldwell--Langlois / Thorne attribution retained.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base using (ℚ; 1ℚ; _+_; _*_; -_; _/_)
open import Data.Rational.Tactic.RingSolver using (solve)
import DASHI.Physics.Gravity.KSW668AdS5TTMultipoleAngularRationalExact as Angular
import DASHI.Physics.Gravity.KSW668F8TTSymbolDiscreteCompatibilityExact as TT

two four six : ℚ
two = (+ 2) / 1
four = (+ 4) / 1
six = (+ 6) / 1

sq : ℚ → ℚ
sq a = a * a

r2 r3 r4 : ℚ → ℚ
r2 r = sq r
r3 r = r2 r * r
r4 r = r2 r * r2 r

-- Original FULL TT Fourier polynomial before any angular projection.
originalCartesianYYPolynomial :
  (x y z : ℚ) →
  TT.ttYY x y z
  ≡ x * x * x * x
    + ((+ 1) / 2) * x * x * y * y
    + ((+ 3) / 2) * x * x * z * z
    + - (((+ 1) / 2) * y * y * z * z)
    + ((+ 1) / 2) * z * z * z * z
originalCartesianYYPolynomial x y z = solve []

-- The transverse-azimuthal averaging uses the original exact
-- rational circle moments <y²>=1/2, <y²z²>=1/8, <z⁴>=3/8.
-- The general analytic circle integral is NOT redefined here.
originalD3AngularFactor : ℚ → ℚ
originalD3AngularFactor mu = two + six * sq mu

originalD3AngularLegendre :
  (mu : ℚ) →
  originalD3AngularFactor mu
    ≡ four * Angular.p0 mu + four * Angular.p2 mu
originalD3AngularLegendre mu = solve []

-- J2=r^4 D²f, J3=r^6 D³f, J4=r^8 D⁴f.
J2 : ℚ → ℚ → ℚ → ℚ
J2 r f1 f2 = r2 r * f2 + - (r * f1)

J3 : ℚ → ℚ → ℚ → ℚ → ℚ
J3 r f1 f2 f3 =
  r3 r * f3 + - (((+ 3) / 1) * r2 r * f2)
    + ((+ 3) / 1) * r * f1

J4 : ℚ → ℚ → ℚ → ℚ → ℚ → ℚ
J4 r f1 f2 f3 f4 =
  r4 r * f4 + - (six * r3 r * f3)
    + ((+ 15) / 1) * r2 r * f2
    + - (((+ 15) / 1) * r * f1)

-- r^4 times the original azimuth-averaged TT yy source.
r4OriginalProjectedCartesianYY :
  ℚ → ℚ → ℚ → ℚ → ℚ → ℚ → ℚ
r4OriginalProjectedCartesianYY mu r f1 f2 f3 f4 =
  six * J2 r f1 f2
    + originalD3AngularFactor mu * J3 r f1 f2 f3
    + Angular.originalTTYYAngular mu * J4 r f1 f2 f3 f4

-- The exact ORIGINAL three scalar Legendre modes, but now DERIVED
-- from the full Cartesian fourth-order TT source via the finite jets.
r4Mode0 : ℚ → ℚ → ℚ → ℚ → ℚ → ℚ
r4Mode0 r f1 f2 f3 f4 =
  six * J2 r f1 f2
    + four * J3 r f1 f2 f3
    + ((+ 2) / 5) * J4 r f1 f2 f3 f4

r4Mode2 : ℚ → ℚ → ℚ → ℚ → ℚ → ℚ
r4Mode2 r f1 f2 f3 f4 =
  four * J3 r f1 f2 f3
    + ((+ 4) / 7) * J4 r f1 f2 f3 f4

r4Mode4 : ℚ → ℚ → ℚ → ℚ → ℚ → ℚ
r4Mode4 r f1 f2 f3 f4 =
  ((+ 1) / 35) * J4 r f1 f2 f3 f4

r4ProjectedTTIsOriginalThreeMultipoles :
  (mu r f1 f2 f3 f4 : ℚ) →
  r4OriginalProjectedCartesianYY mu r f1 f2 f3 f4
    ≡ Angular.p0 mu * r4Mode0 r f1 f2 f3 f4
      + Angular.p2 mu * r4Mode2 r f1 f2 f3 f4
      + Angular.p4 mu * r4Mode4 r f1 f2 f3 f4
r4ProjectedTTIsOriginalThreeMultipoles mu r f1 f2 f3 f4
  = solve []

-- Match the actual original profiles(), WITHOUT changing their
-- normalization or the ell4 conservation remainder.
originalProfile0Weighted : ℚ → ℚ → ℚ → ℚ → ℚ
originalProfile0Weighted r f2 f3 f4 =
  ((+ 2) / 5) * (r4 r * f4 + four * r3 r * f3)

originalProfile2Weighted : ℚ → ℚ → ℚ → ℚ → ℚ → ℚ
originalProfile2Weighted r f1 f2 f3 f4 =
  ((+ 4) / 7) *
    (r4 r * f4 + r3 r * f3
      + - (six * r2 r * f2) + six * r * f1)

originalProfile4Weighted : ℚ → ℚ → ℚ → ℚ → ℚ → ℚ
originalProfile4Weighted r f1 f2 f3 f4 =
  ((+ 1) / 35) *
    (r4 r * f4 + - (six * r3 r * f3)
      + ((+ 15) / 1) * r2 r * f2
      + - (((+ 15) / 1) * r * f1))

originalCartesianTTToG0 :
  (r f1 f2 f3 f4 : ℚ) →
  r4Mode0 r f1 f2 f3 f4
    ≡ originalProfile0Weighted r f2 f3 f4
originalCartesianTTToG0 r f1 f2 f3 f4 = solve []

originalCartesianTTToG2 :
  (r f1 f2 f3 f4 : ℚ) →
  r4Mode2 r f1 f2 f3 f4
    ≡ originalProfile2Weighted r f1 f2 f3 f4
originalCartesianTTToG2 r f1 f2 f3 f4 = solve []

originalCartesianTTToG4 :
  (r f1 f2 f3 f4 : ℚ) →
  r4Mode4 r f1 f2 f3 f4
    ≡ originalProfile4Weighted r f1 f2 f3 f4
originalCartesianTTToG4 r f1 f2 f3 f4 = solve []
