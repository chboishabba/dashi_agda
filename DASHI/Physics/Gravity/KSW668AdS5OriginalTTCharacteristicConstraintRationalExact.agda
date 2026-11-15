module DASHI.Physics.Gravity.KSW668AdS5OriginalTTCharacteristicConstraintRationalExact where

------------------------------------------------------------------------
-- KSW IX: ORIGINAL a=t AdS5 P=H_T+H_z, M=H_T-H_z and
-- U_T=(1+v)P/2+(1-v)M/2. For the UNWEIGHTED second-order SBP
-- characteristic transport D in both P and M, C=D U-(P-M)/2.
--
-- At every interior normal grid node, SAT_P=SAT_M=0:
--      C_T=0 EXACTLY, even with nonzero Israel Neumann source G.
-- At the weak SAT boundaries, C_T=-(SAT_P-SAT_M)/2 instead.
-- If D_w=D+delta is used in characteristic transports, C_T gains
--       -a deltaP-c deltaM.
-- This source file proves rational coefficient/cancellation algebra,
-- NOT a 5D continuum theorem, global boundary constraint or Agda
-- pinned kernel acceptance. Full finite-grid numerical equality is
-- independently verified by the actual original three-mode Numba stage.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_; -_; _/_)
open import Data.Rational.Tactic.RingSolver using (solve)

half quarter third two three four : ℚ
half = (+ 1) / 2
quarter = (+ 1) / 4
third = (+ 1) / 3
two = (+ 2) / 1
three = (+ 3) / 1
four = (+ 4) / 1

a : ℚ → ℚ
a v = half * (1ℚ + v)

c : ℚ → ℚ
c v = half * (1ℚ + - v)

-- Dp,Dm are physical normal derivatives in fixed moving y coordinates.
-- 'common' includes the identical radial FV and AdS warp in both
-- characteristics; those terms cancel, not assumed to vanish.
-- SATp,SATm are the actual original weak-boundary penalty increments.
originalPhysicalConstraintDerivative :
  (v Dp Dm common SATp SATm : ℚ) →
  a v * Dp + c v * Dm
   + - (half *
     (((1ℚ + v) * Dp + common + SATp)
      + - ((v + - 1ℚ) * Dm + common + SATm)))
  ≡ half * (SATm + - SATp)
originalPhysicalConstraintDerivative v Dp Dm common SATp SATm =
  solve []

originalInteriorConstraintExactlyPropagates :
  (v Dp Dm common : ℚ) →
  a v * Dp + c v * Dm
   + - (half *
     (((1ℚ + v) * Dp + common)
      + - ((v + - 1ℚ) * Dm + common)))
  ≡ 0ℚ
originalInteriorConstraintExactlyPropagates v Dp Dm common =
  solve []

-- deltaP = (D_w-D)P, deltaM=(D_w-D)M.
-- The derivative for the weighted scheme is -a deltaP -c deltaM
-- at interior nodes, not identically zero for a finite grid.
originalWeightedSplitConstraintDefect :
  (v Dp Dm deltaP deltaM common : ℚ) →
  a v * Dp + c v * Dm
   + - (half *
     (((1ℚ + v) * (Dp + deltaP) + common)
      + - ((v + - 1ℚ) * (Dm + deltaM) + common)))
  ≡ - (a v * deltaP) + - (c v * deltaM)
originalWeightedSplitConstraintDefect v Dp Dm deltaP deltaM common =
  solve []

-- SSPRK3 convex combinations preserve any LINEAR C whose stage
-- derivatives are zero at a fixed finite-grid interior node:
-- 1/3 X0 + 2/3 (3/4 X0 +1/4 X0) = X0.
originalThreeStageSSPRK3ConstraintCombination :
  (C0 : ℚ) →
  third * C0
  + ((two * third) * ((three * quarter) * C0 + quarter * C0))
  ≡ C0
originalThreeStageSSPRK3ConstraintCombination C0 = solve []

-- The actual second-order diagonal SBP SAT has H_wall=dy/2.
-- SAT_M=(1-v)/H_wall * (M_target-M_wall), so
--      dy * Cdot_wall=(1+v)P_wall-(1-v)M_wall-2G.
-- At the weak outgoing remote boundary dy*Cdot_far=(1+v)P_far.
-- The exact rational original t=4/3 initial constrained state
-- U=y/2, P=1, M=0, G=0 has wall and far constraint rate
-- (2/5)/dy even though all initial C nodes are zero.
originalWallConstraintSATResidual :
  (v P M G : ℚ) →
  ((1ℚ + v) * P + - ((1ℚ + - v) * M) + - (two * G))
    ≡ ((1ℚ + v) * P)
       + - ((1ℚ + - v) * M + two * G)
originalWallConstraintSATResidual v P M G = solve []

originalT43WeakWallConstraintNoGo :
  ((1ℚ + - ((+ 3) / 5)) * 1ℚ)
  ≡ (+ 2) / 5
originalT43WeakWallConstraintNoGo = solve []
