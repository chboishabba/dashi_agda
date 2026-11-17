module DASHI.Physics.Gravity.KSW668F8SSPRK3FullStabilityPrerequisiteExact where

------------------------------------------------------------------------
-- Max-cut XXIX: explicit rational CFL negative control, complementing
-- the existing exact imaginary-axis SSPRK3 owner. NOT a general moving
-- AdS5 (P,M,U) stability theorem. In particular radial-only and normal-
-- only energy receipts cannot be promoted without a coupled bound.
--
-- SSPRK3 R(z)=1+z+z²/2+z³/6.
-- For scalar damping y'= -k y and timestep dt, q=k dt=3 gives
-- R(-3)=-2 (absolute amplification 2>1). Thus SSPRK3 is not
-- unconditionally stable even for a dissipative scalar mode.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base using (ℚ; 1ℚ; _+_; _*_; -_; _/_)
open import Data.Rational.Tactic.RingSolver using (solve)
import DASHI.Physics.Gravity.KSW668AdS5RadialSSPRK3ImaginaryPolynomialExact as Radial
import DASHI.Physics.Gravity.KSW668AdS5MovingNormalFiniteSBPTelescopeExact as Normal

half sixth : ℚ
half = (+ 1) / 2
sixth = (+ 1) / 6

ssprk3RealPolynomial : ℚ → ℚ
ssprk3RealPolynomial z =
  1ℚ + z + half * z * z + sixth * z * z * z

scalarDampingAtThree :
  ssprk3RealPolynomial (- ((+ 3) / 1))
    ≡ - ((+ 2) / 1)
scalarDampingAtThree = solve []

scalarDampingAmplificationSquared :
  ssprk3RealPolynomial (- ((+ 3) / 1))
    * ssprk3RealPolynomial (- ((+ 3) / 1))
    ≡ (+ 4) / 1
scalarDampingAmplificationSquared = solve []

data F8MovingCoupledStabilityHole : Set where
  movingAdS5WeightedSymmetrizer : F8MovingCoupledStabilityHole
  discreteTimeAndWarpCommutatorBound : F8MovingCoupledStabilityHole
  SBP2SATRadialMixedBoundaryClosures : F8MovingCoupledStabilityHole
  meshUniformSourceToBothWeylTrace : F8MovingCoupledStabilityHole
