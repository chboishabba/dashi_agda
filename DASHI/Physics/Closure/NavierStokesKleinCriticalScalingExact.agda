module DASHI.Physics.Closure.NavierStokesKleinCriticalScalingExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- James Serrin,
-- "On the Interior Regularity of Weak Solutions of the Navier--Stokes
-- Equations", Archive for Rational Mechanics and Analysis 9 (1962), 187--195.
-- DOI: 10.1007/BF00253344.
--
-- J. T. Beale, T. Kato and A. Majda,
-- "Remarks on the Breakdown of Smooth Solutions for the 3-D Euler
-- Equations", Communications in Mathematical Physics 94 (1984), 61--66.
-- DOI: 10.1007/BF01212349.
--
-- Felix Klein's Erlangen viewpoint is used here only as an organizing
-- principle: identify the transformation action first, then identify the
-- quantities invariant under it.
--
-- DASHI CONTRIBUTION
--
-- Check the exact rational exponent arithmetic for the three-dimensional
-- Navier--Stokes scaling
--
--   u_lambda(x,t) = lambda u(lambda x, lambda^2 t).
--
-- The spatial L^p exponent is 1-3/p and the Serrin mixed-norm defect is
-- 2/q+3/p-1.  The standard critical endpoints are checked exactly.  This is a
-- scaling classifier, not a regularity theorem and not an estimate on an
-- actual solution.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _/_)
open import Data.Rational.Tactic.RingSolver using (solve)

velocityLpScalingExponent : ℚ → ℚ
velocityLpScalingExponent reciprocalP =
  1ℚ - (+ 3 / 1) * reciprocalP

pressureLpScalingExponent : ℚ → ℚ
pressureLpScalingExponent reciprocalP =
  (+ 2 / 1) - (+ 3 / 1) * reciprocalP

serrinScalingDefect : ℚ → ℚ → ℚ
serrinScalingDefect reciprocalQ reciprocalP =
  (+ 2 / 1) * reciprocalQ
  + (+ 3 / 1) * reciprocalP
  - 1ℚ

velocityL3CriticalExact :
  velocityLpScalingExponent (+ 1 / 3) ≡ 0ℚ
velocityL3CriticalExact = solve []

velocityLInfinityExponentExact :
  velocityLpScalingExponent 0ℚ ≡ 1ℚ
velocityLInfinityExponentExact = solve []

pressureLThreeHalvesCriticalExact :
  pressureLpScalingExponent (+ 2 / 3) ≡ 0ℚ
pressureLThreeHalvesCriticalExact = solve []

serrinLInfinityTimeL3SpaceExact :
  serrinScalingDefect 0ℚ (+ 1 / 3) ≡ 0ℚ
serrinLInfinityTimeL3SpaceExact = solve []

serrinL2TimeLInfinitySpaceExact :
  serrinScalingDefect (+ 1 / 2) 0ℚ ≡ 0ℚ
serrinL2TimeLInfinitySpaceExact = solve []

serrinL4TimeL6SpaceExact :
  serrinScalingDefect (+ 1 / 4) (+ 1 / 6) ≡ 0ℚ
serrinL4TimeL6SpaceExact = solve []

serrinDefectAffineExact : ∀ qInv pInv qShift pShift →
  serrinScalingDefect (qInv + qShift) (pInv + pShift)
  ≡ serrinScalingDefect qInv pInv
    + (+ 2 / 1) * qShift + (+ 3 / 1) * pShift
serrinDefectAffineExact qInv pInv qShift pShift =
  solve (qInv ∷ pInv ∷ qShift ∷ pShift ∷ [])

data ScalingClassification : Set where
  subcritical critical supercritical : ScalingClassification

criticalSerrinSurface : ScalingClassification
criticalSerrinSurface = critical
