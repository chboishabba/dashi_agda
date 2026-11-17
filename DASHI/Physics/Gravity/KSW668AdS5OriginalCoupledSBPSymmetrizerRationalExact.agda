module DASHI.Physics.Gravity.KSW668AdS5OriginalCoupledSBPSymmetrizerRationalExact where

------------------------------------------------------------------------
-- KSW original a=t moving AdS5 TT, common (P,M,U) symmetrizer algebra.
--
-- Mathematical producer (not yet an Agda-kernel-accepted continuum proof):
-- a=(1+v)/2, c=(1-v)/2, E=1/2 Sum Hy z^-3 Vr
--                         (aP²+cM²+U(-Lr)U).
-- Weight-split normal SBP plus exact FV radial Green cancels Lr work;
-- the AdS warp and the moving z^-3 weight cancel all but
--      3v/(2z) (P*M - radialGradientEnergy).
-- Neumann SAT wall gives exact homogeneous negative square
--   -1/4 ((1+v)P-(1-v)M)^2,
-- and NONZERO source adds -(1-v)M G, not a C G² bound.
--
-- This module proves the rational POLYNOMIAL algebra only. The real
-- weighted-SBP, FV Green, time derivative, sqrt(v(t)) and uniform
-- Gronwall estimate are separately tested and documented; pinned
-- Agda 2.9 kernel NOT run. No Weyl/SSPRK3 physical promotion.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_; -_; _/_)
open import Data.Rational.Tactic.RingSolver using (solve)
import DASHI.Physics.Gravity.KSW668AdS5MovingNormalFiniteSBPTelescopeExact as SBP
import DASHI.Physics.Gravity.KSW668AdS5TTFiniteVolumeFirstCellRationalExact as FV

half two three : ℚ
half = (+ 1) / 2
two = (+ 2) / 1
three = (+ 3) / 1

kineticPlus : ℚ → ℚ
kineticPlus v = half * (1ℚ + v)

kineticMinus : ℚ → ℚ
kineticMinus v = half * (1ℚ + - v)

square : ℚ → ℚ
square x = x * x

-- The reciprocal-z factor is an independent positive real quantity
-- in the continuum; its rational polynomial identity has no division.
fullMovingWarpWeightCancellation :
  ∀ (v p m radial inverseZ : ℚ) →
  (half * three * inverseZ)
    * ((kineticPlus v * (1ℚ + v) * square p)
       + (kineticMinus v * (v + - 1ℚ) * square m)
       + - ((kineticPlus v * p + kineticMinus v * m)
             * (p + - m))
       + - (v * (kineticPlus v * square p
                  + kineticMinus v * square m + radial)))
  ≡ (half * three * inverseZ) * v * (p * m + - radial)
fullMovingWarpWeightCancellation v p m radial inverseZ = solve []

weightedSATWallFlux : ℚ → ℚ → ℚ → ℚ → ℚ
weightedSATWallFlux v p m G =
  - (half * kineticPlus v * (1ℚ + v) * square p)
  + half * kineticMinus v * (1ℚ + - v) * square m
  + kineticMinus v * m
      * ((1ℚ + v) * p + - (two * G)
         + - ((1ℚ + - v) * m))

originalForcedWallExactSquare :
  ∀ (v p m G : ℚ) →
  weightedSATWallFlux v p m G
    + half * half
        * square ((1ℚ + v) * p + - ((1ℚ + - v) * m))
    + (1ℚ + - v) * m * G
  ≡ 0ℚ
originalForcedWallExactSquare v p m G = solve []

-- Purely algebraic cancellation behind the boundary-source lift.
-- At the physical moving wall choose lift L with (1-v)L=-2G.
originalCharacteristicLiftCancelsSource :
  ∀ (v p m G L : ℚ) →
  ((1ℚ + v) * p
     + - ((1ℚ + - v) * (m + L))
     + - (two * G))
  ≡ ((1ℚ + v) * p
      + - ((1ℚ + - v) * m))
     + - ((1ℚ + - v) * L + two * G)
originalCharacteristicLiftCancelsSource v p m G L = solve []
