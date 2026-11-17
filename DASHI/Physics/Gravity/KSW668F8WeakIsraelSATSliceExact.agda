module DASHI.Physics.Gravity.KSW668F8WeakIsraelSATSliceExact where

------------------------------------------------------------------------
-- Max-cut XXIX: exact ORIGINAL normal_order=3 SAT at rational t=4/3.
-- Reuses original moving a=t characteristic v=-3/5, with a nominal
-- normal mesh dy=0.012 = 3/250. SAT target and injection come directly
-- from scripts/ksw668_f8_tt_multipole.py, not a new boundary operator.
--
-- v=-3/5, 1+v=2/5, v-1=-8/5.
-- target = (2 amp S -(1+v) P)/(v-1)
--        = -5/4 amp S + 1/4 P.
-- 2(1-v)/dy = 800/3.
-- SAT_M = -1000/3 amp S + 200/3 P -800/3 M.
-- This is exact finite-stage wall algebra, NOT all-(P,M,U) energy or
-- strong enforcement. The stage RHS includes the non-SAT normal
-- derivative and radial/warp force in addition to this correction.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base using (ℚ; _/_; _+_; _*_; -_)
open import Data.Rational.Tactic.RingSolver using (solve)
import DASHI.Physics.Gravity.KSW668AdS5MovingNeumannCharacteristicRationalExact as Normal

sliceV : ℚ
sliceV = - ((+ 3) / 5)

sliceDY : ℚ
sliceDY = (+ 3) / 250

slicePenalty : ℚ
slicePenalty = (+ 800) / 3

weakIsraelTarget : ℚ → ℚ → ℚ → ℚ
weakIsraelTarget amp src p =
  - (((+ 5) / 4) * amp * src)
    + ((+ 1) / 4) * p

weakIsraelSAT : ℚ → ℚ → ℚ → ℚ → ℚ
weakIsraelSAT amp src p m =
  slicePenalty * (weakIsraelTarget amp src p + - m)

weakIsraelTargetSourceCompatible :
  (amp src p : ℚ) →
  ((- ((+ 8) / 5)) * weakIsraelTarget amp src p)
    ≡ (((+ 2) / 1) * amp * src)
      + - (((+ 2) / 5) * p)
weakIsraelTargetSourceCompatible amp src p = solve []

weakIsraelSATExactInjection :
  (amp src p m : ℚ) →
  weakIsraelSAT amp src p m
    ≡ - (((+ 1000) / 3) * amp * src)
      + ((+ 200) / 3) * p
      + - (((+ 800) / 3) * m)
weakIsraelSATExactInjection amp src p m = solve []

sliceVelocityMatchesOriginal :
  sliceV ≡ Normal.originalWallVelocity
sliceVelocityMatchesOriginal = solve []

data F8FullCoupledSATOpenGate : Set where
  movingTimeDependentSymmetrizer :
    F8FullCoupledSATOpenGate
  radialNormalCoupledBoundaryEnergy :
    F8FullCoupledSATOpenGate
  fullSSPRK3BoundaryPenaltyCompatibility :
    F8FullCoupledSATOpenGate
