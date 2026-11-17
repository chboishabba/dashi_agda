module DASHI.Physics.Gravity.KSW668F8RadialConjugationNoncommutationExact where

------------------------------------------------------------------------
-- Max-cut XXXII: exact negative control for UNPROVED discrete
-- Cartesian-to-original-effective-radial-FV commuting square.
--
-- In continuum, for ell=2,4:
--  [d²/dr²+2/r d/dr-ell(ell+1)/r²](r^ell V)
--     =r^ell [d²/dr²+(2ell+2)/r d/dr]V .
-- Original F8 evolves V by weighted effective d=7/11 shell FV.
--
-- A NAIVE comparison: evolve H=r^ell V by separate d=3 shell FV,
-- subtract ell(ell+1)H/r² at the first INTERIOR shell r=h,
-- versus r^ell times original d=(3+2ell) FV evolution of V.
-- With h=eps=1, ell2 and V=r², or ell4 and V=1, their difference
-- is exactly 142/13. Thus this natural naive diagram does NOT
-- commute, even for polynomial data on the same node coordinates.
--
-- This does NOT assert the physical original solver fails tensor TT:
-- it never runs the naive d=3 FV tensor alternative. It highlights
-- the *required* compatible full-tensor reconstruction as open G1.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base using (ℚ; _+_; _*_; -_; _/_)
open import Data.Rational.Tactic.RingSolver using (solve)
import DASHI.Physics.Gravity.KSW668AdS5TTFiniteVolumeFirstCellRationalExact as FV

-- At j=1 and h=1, original d=3 FV applied to r^4:
--  cp*(2^4-1^4) - cm*(1^4-0^4).
naiveThreeDimensionalFVQuarticAtFirst : ℚ
naiveThreeDimensionalFVQuarticAtFirst =
  ((+ 15) / 1) * FV.d3Plus + - FV.d3Minus

-- Ell=2, V=r², H=r² V=r⁴. Naive 3D FV plus -6/r² H
-- vs original d7 FV V=14 multiplied by r²=1.
ell2NaiveConjugationDefect :
  naiveThreeDimensionalFVQuarticAtFirst
    + - ((+ 6) / 1)
    + - ((+ 14) / 1)
    ≡ (+ 142) / 13
ell2NaiveConjugationDefect = solve []

-- Ell=4, V=1, H=r⁴. Naive 3D FV plus -20/r² H
-- vs original d11 FV of constant V=0.
ell4NaiveConjugationDefect :
  naiveThreeDimensionalFVQuarticAtFirst
    + - ((+ 20) / 1)
    ≡ (+ 142) / 13
ell4NaiveConjugationDefect = solve []
