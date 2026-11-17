module DASHI.Physics.Gravity.KSW668F8FullTensorSolidHarmonicAtlasExact where

------------------------------------------------------------------------
-- XXXIV original KSW668 FOURTH-ORDER full 3x3 TT Fourier tensor atlas.
-- REUSE exact owner KSW668F8TTSymbolDiscreteCompatibilityExact.
--
-- Homogeneous degree-four REAL solid associated-Legendre polynomials,
-- Condon-Shortley convention; angular ell=0,2,4 only, but azimuth
-- m=0,1,2,3,4 and sine/cosine sectors.
--
-- IMPORTANT: The existing F8 radial FV solver evolves the azimuthally
-- projected yy scalar observer, not all six Cartesian tensor fields.
-- Algebraic atlas ≠ discretely commuting tensor-to-FV projection,
-- full tensor energy, Agda kernel acceptance, or physical observation.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base using (ℚ; _+_; _*_; -_; _/_)
open import Data.Rational.Tactic.RingSolver using (solve)
import DASHI.Physics.Gravity.KSW668F8TTSymbolDiscreteCompatibilityExact as TT
import DASHI.Physics.Gravity.KSW668AdS5TTMultipoleAngularRationalExact as Angular

K : ℚ → ℚ → ℚ → ℚ
K x y z = x * x + y * y + z * z

h00 h20 h40 h21c h21s h41c h41s h22c h42c h43c h43s h44c h44s :
  ℚ → ℚ → ℚ → ℚ

h00 x y z = K x y z * K x y z
h20 x y z =
  ((+ 1) / 2) * K x y z * (((+ 3) / 1) * x * x + - K x y z)
h40 x y z =
  ((+ 1) / 8) * (((+ 35) / 1) * x * x * x * x
    + - (((+ 30) / 1) * K x y z * x * x)
    + ((+ 3) / 1) * K x y z * K x y z)
h21c x y z = - (((+ 3) / 1) * K x y z * x * y)
h21s x y z = - (((+ 3) / 1) * K x y z * x * z)
h41c x y z =
  - (((+ 5) / 2) * x * (((+ 7) / 1) * x * x
      + - (((+ 3) / 1) * K x y z)) * y)
h41s x y z =
  - (((+ 5) / 2) * x * (((+ 7) / 1) * x * x
      + - (((+ 3) / 1) * K x y z)) * z)
h22c x y z = ((+ 3) / 1) * K x y z * (y * y + - (z * z))
h42c x y z =
  ((+ 15) / 2) * (((+ 7) / 1) * x * x + - K x y z)
    * (y * y + - (z * z))
h43c x y z =
  - (((+ 105) / 1) * x * (y * y * y + - (((+ 3) / 1) * y * z * z)))
h43s x y z =
  - (((+ 105) / 1) * x * (((+ 3) / 1) * y * y * z + - (z * z * z)))
h44c x y z =
  ((+ 105) / 1) * (y * y * y * y
    + - (((+ 6) / 1) * y * y * z * z) + z * z * z * z)
h44s x y z =
  ((+ 420) / 1) * y * z * (y * y + - (z * z))

atlasXX atlasXY atlasXZ atlasYY atlasYZ atlasZZ :
  ℚ → ℚ → ℚ → ℚ
atlasXX x y z =
  ((+ 4) / 21) * h22c x y z
    + ((+ 1) / 105) * h42c x y z
atlasXY x y z =
  ((+ 2) / 7) * h21c x y z
    + ((+ 1) / 70) * h41c x y z
    + - (((+ 1) / 420) * h43c x y z)
atlasXZ x y z =
  - (((+ 2) / 7) * h21s x y z)
    + - (((+ 1) / 70) * h41s x y z)
    + - (((+ 1) / 420) * h43s x y z)
atlasYY x y z =
  ((+ 2) / 5) * h00 x y z
    + ((+ 4) / 7) * h20 x y z
    + ((+ 1) / 35) * h40 x y z
    + - (((+ 2) / 21) * h22c x y z)
    + - (((+ 1) / 210) * h42c x y z)
    + ((+ 1) / 840) * h44c x y z
atlasYZ x y z = ((+ 1) / 840) * h44s x y z
atlasZZ x y z =
  - (((+ 2) / 5) * h00 x y z)
    + - (((+ 4) / 7) * h20 x y z)
    + - (((+ 1) / 35) * h40 x y z)
    + - (((+ 2) / 21) * h22c x y z)
    + - (((+ 1) / 210) * h42c x y z)
    + - (((+ 1) / 840) * h44c x y z)

-- Exact full tensor component atlas, including non-axisymmetric modes.
fullOriginalTensorXX :
  (x y z : ℚ) → TT.ttXX x y z ≡ atlasXX x y z
fullOriginalTensorXX x y z = solve []

fullOriginalTensorXY :
  (x y z : ℚ) → TT.ttXY x y z ≡ atlasXY x y z
fullOriginalTensorXY x y z = solve []

fullOriginalTensorXZ :
  (x y z : ℚ) → TT.ttXZ x y z ≡ atlasXZ x y z
fullOriginalTensorXZ x y z = solve []

fullOriginalTensorYY :
  (x y z : ℚ) → TT.ttYY x y z ≡ atlasYY x y z
fullOriginalTensorYY x y z = solve []

fullOriginalTensorYZ :
  (x y z : ℚ) → TT.ttYZ x y z ≡ atlasYZ x y z
fullOriginalTensorYZ x y z = solve []

fullOriginalTensorZZ :
  (x y z : ℚ) → TT.ttZZ x y z ≡ atlasZZ x y z
fullOriginalTensorZZ x y z = solve []

-- The m=0 yy harmonic is EXACTLY the existing original F8
-- radial-source polynomial. Nonzero azimuthal sectors integrate
-- to zero for a rotationally symmetric scalar prepotential on-axis.
yyAxialZeroMode : ℚ → ℚ → ℚ → ℚ
yyAxialZeroMode x y z =
  ((+ 2) / 5) * h00 x y z
    + ((+ 4) / 7) * h20 x y z
    + ((+ 1) / 35) * h40 x y z

yyAxialZeroModePolynomial :
  (x y z : ℚ) →
  yyAxialZeroMode x y z
    ≡ ((+ 1) / 8) * (x * x * x * x
       + ((+ 6) / 1) * K x y z * x * x
       + K x y z * K x y z)
yyAxialZeroModePolynomial x y z = solve []

yyAxisFullTensor :
  (x : ℚ) → TT.ttYY x ((+ 0) / 1) ((+ 0) / 1)
    ≡ x * x * x * x
yyAxisFullTensor x = solve []

-- Angular projection as an integral and physical receiver propagation
-- still require an independently accepted calculus / FV commuting map.
