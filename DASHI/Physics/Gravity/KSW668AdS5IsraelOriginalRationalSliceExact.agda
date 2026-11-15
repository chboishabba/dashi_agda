module DASHI.Physics.Gravity.KSW668AdS5IsraelOriginalRationalSliceExact where

------------------------------------------------------------------------
-- Original 5D AdS thin FRW brane: a(t)=t, ell=1, sigma=1,
-- Lambda5=-6, kappa5^2=6 (Caldwell-Langlois 2001).
-- DOI: 10.1016/S0370-2693(01)00631-1.
--
-- Exact source-metric FRW time SLICE at t=4/3:
-- sqrt(1+t^-2)=5/4 exactly, H=3/4.
-- rho=A-1=1/4, pressure=-1/10, rho+p=3/20.
-- mixed matter/tension source S^a_b is diag(-5/4,-11/10,...);
-- trace S=-91/20, and geometry's mixed extrinsic curvature is
-- diag(-4/5,-5/4,-5/4,-5/4).
--
-- Standard Z2 5D Israel equation
-- K^a_b= - kappa5²/2 (S^a_b-delta^a_b S/3)
--      = -3*S^a_b + delta^a_b*S
-- is certified at ALL 16 component positions by finite exact rational
-- case splitting below, not by a Boolean claim or a free K parameter.
--
-- This is a sourced rational 4D slice. It is NOT a kernel-checked
-- differentiated 5D metric, full continuum junction distribution,
-- unique physical brane, perturbative stability or detected bulk ray.
-- No conflation with existing GRQFT 4D Kottler thin 2+1D shell:
-- that shell has a different intrinsic/extrinsic dimension.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_; -_; _/_)
open import Data.Rational.Tactic.RingSolver using (solve)
import DASHI.Physics.Foundations.GRQFTIsraelBranchMaxCutExact as KottlerShell
import DASHI.Physics.Closure.MonsterGravityAuthorityAndDimensionExact as Monster

originalTime : ℚ
originalTime = (+ 4) / 3

originalH : ℚ
originalH = (+ 3) / 4

originalA : ℚ
originalA = (+ 5) / 4

originalRho : ℚ
originalRho = (+ 1) / 4

originalPressure : ℚ
originalPressure = - ((+ 1) / 10)

originalTension : ℚ
originalTension = 1ℚ

originalRhoPlusP : ℚ
originalRhoPlusP = originalRho + originalPressure

originalNECIsThreeTwentieths :
  originalRhoPlusP ≡ (+ 3) / 20
originalNECIsThreeTwentieths = solve []

originalFriedmannAtSelectedTime :
  (originalH * originalH)
    ≡ ((originalRho + originalTension)
        * (originalRho + originalTension)) + - 1ℚ
originalFriedmannAtSelectedTime = solve []

data BraneAxis4 : Set where
  τ x y z : BraneAxis4

delta4 : BraneAxis4 → BraneAxis4 → ℚ
delta4 τ τ = 1ℚ
delta4 x x = 1ℚ
delta4 y y = 1ℚ
delta4 z z = 1ℚ
delta4 _ _ = 0ℚ

-- Mixed source tensor S^a_b = diag(-rho-sigma,p-sigma,p-sigma,p-sigma).
sourceMixed : BraneAxis4 → BraneAxis4 → ℚ
sourceMixed τ τ = - ((+ 5) / 4)
sourceMixed x x = - ((+ 11) / 10)
sourceMixed y y = - ((+ 11) / 10)
sourceMixed z z = - ((+ 11) / 10)
sourceMixed _ _ = 0ℚ

sourceTrace : ℚ
sourceTrace =
  sourceMixed τ τ
    + sourceMixed x x
    + sourceMixed y y
    + sourceMixed z z

sourceTraceExactlyMinus91over20 :
  sourceTrace ≡ - ((+ 91) / 20)
sourceTraceExactlyMinus91over20 = solve []

-- Geometric K^a_b from the explicit inward AdS unit normal.
originalGeometricK : BraneAxis4 → BraneAxis4 → ℚ
originalGeometricK τ τ = - ((+ 4) / 5)
originalGeometricK x x = - ((+ 5) / 4)
originalGeometricK y y = - ((+ 5) / 4)
originalGeometricK z z = - ((+ 5) / 4)
originalGeometricK _ _ = 0ℚ

-- Under kappa5²=6, the exact Z2 Israel tensor equation reduces to
-- -3 S^a_b + delta^a_b Trace(S).
originalIsraelSource : BraneAxis4 → BraneAxis4 → ℚ
originalIsraelSource a b =
  - (((+ 3) / 1) * sourceMixed a b)
    + sourceTrace * delta4 a b

-- Each clause matches a distinct actual (row,column) tensor component.
-- The twelve off-diagonal zeros are included explicitly.
originalIsraelAllSixteenComponents :
  (a b : BraneAxis4) →
  originalGeometricK a b ≡ originalIsraelSource a b
originalIsraelAllSixteenComponents τ τ = solve []
originalIsraelAllSixteenComponents τ x = solve []
originalIsraelAllSixteenComponents τ y = solve []
originalIsraelAllSixteenComponents τ z = solve []
originalIsraelAllSixteenComponents x τ = solve []
originalIsraelAllSixteenComponents x x = solve []
originalIsraelAllSixteenComponents x y = solve []
originalIsraelAllSixteenComponents x z = solve []
originalIsraelAllSixteenComponents y τ = solve []
originalIsraelAllSixteenComponents y x = solve []
originalIsraelAllSixteenComponents y y = solve []
originalIsraelAllSixteenComponents y z = solve []
originalIsraelAllSixteenComponents z τ = solve []
originalIsraelAllSixteenComponents z x = solve []
originalIsraelAllSixteenComponents z y = solve []
originalIsraelAllSixteenComponents z z = solve []

-- Source labels for explicit four-dimensional Kottler vs FIVE-dimensional
-- AdS comparison; the two Israel systems are not isomorphic by name.
original4DKottlerIsraelOwner :
  KottlerShell.IsraelBranchMaxCut
original4DKottlerIsraelOwner =
  KottlerShell.canonicalIsraelBranchMaxCut

originalMonsterGravityRouteOwner :
  Monster.GravityRouteDescriptor
originalMonsterGravityRouteOwner =
  Monster.wittenAdS3MonsterRoute

-- Monster AdS3/CFT and AdS5 cosmological-3-brane are dimensionally and
-- dynamically separate. This module does NOT derive any physical 5D KK
-- field, junction, string UV completion or Monster gravitational spectrum
-- from the other owner's imported existence or attribution receipt.
