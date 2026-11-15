module DASHI.Physics.Gravity.KSW668AdS5TTFiniteVolumeFirstCellRationalExact where

------------------------------------------------------------------------
-- ORIGINAL a=t AdS5 compact TT three-radial-multipole discretization.
-- Effective radial dimensions d = 3, 7, 11 arise from ell=0,2,4,
-- NOT additional physical bulk dimensions.
--
-- Correct finite-volume j=1 radial coefficients:
-- cp_d = d*(3/2)^(d-1) / ((3/2)^d - (1/2)^d)
-- cm_d = d*(1/2)^(d-1) / ((3/2)^d - (1/2)^d)
-- The exact r² test is 3 cp_d - cm_d = 2d.
-- Contrast old centre-volume coefficients, which gave
-- 6.5 / 34.15625 / 172.99414 instead of 6 / 14 / 22.
--
-- This owner proves the concrete rational first-cell identities;
-- general shell-volume summation-by-parts and continuum error transfer
-- remain analytic/kernel obligations, NOT asserted here.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base using (ℚ; _/_; _+_; _*_; -_)
open import Data.Rational.Tactic.RingSolver using (solve)

d3Plus d3Minus : ℚ
d3Plus = (+ 27) / 13
d3Minus = (+ 3) / 13

d7Plus d7Minus : ℚ
d7Plus = (+ 5103) / 1093
d7Minus = (+ 7) / 1093

d11Plus d11Minus : ℚ
d11Plus = (+ 649539) / 88573
d11Minus = (+ 11) / 88573

originalD3ExactQuadratic :
  ((+ 3) / 1) * d3Plus + - d3Minus ≡ (+ 6) / 1
originalD3ExactQuadratic = solve []

originalD7ExactQuadratic :
  ((+ 3) / 1) * d7Plus + - d7Minus ≡ (+ 14) / 1
originalD7ExactQuadratic = solve []

originalD11ExactQuadratic :
  ((+ 3) / 1) * d11Plus + - d11Minus ≡ (+ 22) / 1
originalD11ExactQuadratic = solve []
