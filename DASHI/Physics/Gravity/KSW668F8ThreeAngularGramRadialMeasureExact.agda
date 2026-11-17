module DASHI.Physics.Gravity.KSW668F8ThreeAngularGramRadialMeasureExact where

------------------------------------------------------------------------
-- Max-cut XXXII: ORIGINAL yy scalar angular P0/P2/P4 Gram certificate.
-- Reuse existing owner KSW668AdS5TTMultipoleAngularRationalExact.
-- Orthogonality under integral dmu on [-1,1] is certified using
-- exact rational moments m_(2j) = 2/(2j+1), j=0..4.
--
-- On H_l(r)= (r/eps)^l V_l(r), the yy scalar angular norm
-- (with the ordinary 3D radial r² dr and dmu, omitting azimuth 2pi)
-- is diagonal:
--  Sum_{ell=0,2,4} [2/(2ell+1)] eps^(-2ell)
--      integral r^(2+2ell) |V_ell(r)|² dr.
-- These are exactly d=3,7,11 effective radial volume measures.
--
-- This proves the FINITE angular Gram algebra only. In particular,
-- the full 3x3 TT tensor norm has different index contractions, and
-- the original FV shell weights/pointwise readout require separate
-- commuting quadrature/embedding witnesses. Agda kernel pending.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base using (ℚ; _+_; _*_; -_; _/_)
open import Data.Rational.Tactic.RingSolver using (solve)
import DASHI.Physics.Gravity.KSW668AdS5TTMultipoleAngularRationalExact as Angular

m0 m2 m4 m6 m8 : ℚ
m0 = (+ 2) / 1
m2 = (+ 2) / 3
m4 = (+ 2) / 5
m6 = (+ 2) / 7
m8 = (+ 2) / 9

gram00 gram02 gram04 gram22 gram24 gram44 : ℚ
gram00 = m0
gram02 = (((+ 3) / 1) * m2 + - m0) * ((+ 1) / 2)
gram04 =
  (((+ 35) / 1) * m4 + - (((+ 30) / 1) * m2)
    + ((+ 3) / 1) * m0) * ((+ 1) / 8)
gram22 =
  (((+ 9) / 1) * m4 + - (((+ 6) / 1) * m2) + m0)
    * ((+ 1) / 4)
gram24 =
  (((+ 105) / 1) * m6 + - (((+ 125) / 1) * m4)
    + ((+ 39) / 1) * m2 + - (((+ 3) / 1) * m0))
    * ((+ 1) / 16)
gram44 =
  (((+ 1225) / 1) * m8 + - (((+ 2100) / 1) * m6)
    + ((+ 1110) / 1) * m4 + - (((+ 180) / 1) * m2)
    + ((+ 9) / 1) * m0)
    * ((+ 1) / 64)

originalAngularGram00 : gram00 ≡ (+ 2) / 1
originalAngularGram00 = solve []
originalAngularGram02 : gram02 ≡ (+ 0) / 1
originalAngularGram02 = solve []
originalAngularGram04 : gram04 ≡ (+ 0) / 1
originalAngularGram04 = solve []
originalAngularGram22 : gram22 ≡ (+ 2) / 5
originalAngularGram22 = solve []
originalAngularGram24 : gram24 ≡ (+ 0) / 1
originalAngularGram24 = solve []
originalAngularGram44 : gram44 ≡ (+ 2) / 9
originalAngularGram44 = solve []
