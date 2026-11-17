module DASHI.Physics.Gravity.KSW668F8MovingSBP2SATBoundaryEnergyExact where

------------------------------------------------------------------------
-- XXXVIII: exact ORIGINAL normal_order=3 SBP2 weak-Israel SAT energy.
--
-- Source: scripts/ksw668_f8_tt_multipole.py, stage(), not a generic
-- first-order upwind scheme. At iy=0,N the normal derivative D uses
-- a one-sided first difference; at interior nodes it uses centered
-- differences. The diagonal SBP norm is dy*(1/2,1,...,1,1/2).
--
-- P_T=(1+v) D P + force; M_T=(v-1) D M + force.
-- Upper SAT in P: -2(1+v)P_N/dy.
-- Lower SAT in M: +2(1-v)(target-M_0)/dy.
-- Therefore E_N=1/2 ||P||_H^2 +1/2 ||M||_H^2 has an
-- exact NORMAL derivative + SAT boundary contribution:
--
--   -(1+v)/2*(P_0^2+P_N^2)
--   -(1-v)/2*(M_N^2+(M_0-target)^2)
--   +(1-v)/2*target^2 .
--
-- Full E_N' ALSO includes the actual force terms
--   <P+M, L_d U -3(P-M)/(2z)>_H,
-- weighted radial FV sums and moving-domain coefficients.
-- These are NOT silently discarded. No global stability, uniform
-- CFL, or physical G1-G6 theorem follows from boundary algebra.
--
-- At the original time t=4/3, v=-3/5, target=P0/4-5S/4
-- for S=amp*source, the lower contribution equals
--   -4/5*(M0-target)^2
--   -3/20*(P0+5S/3)^2 +5S^2/3 .
-- This is the exact original source cap at the rational slice.
--
-- Reuse original normal SBP telescope and moving Israel SAT owners.
-- Pinned Agda kernel acceptance remains OPEN.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_; -_; _/_)
open import Data.Rational.Tactic.RingSolver using (solve)
import DASHI.Physics.Gravity.KSW668AdS5MovingNormalFiniteSBPTelescopeExact as SBP
import DASHI.Physics.Gravity.KSW668F8WeakIsraelSATSliceExact as Wall

half : ℚ
half = (+ 1) / 2

square : ℚ → ℚ
square x = x * x

-- Facewise identity for the original centered SBP2 norm.
centeredFaceEnergy : ℚ → ℚ → ℚ
centeredFaceEnergy x y =
  half * (x + y) * (y + - x)

centeredFaceEnergyIdentity :
  (x y : ℚ) →
  centeredFaceEnergy x y ≡ half * (square y + - square x)
centeredFaceEnergyIdentity x y = solve []

centeredEnergySum : List ℚ → ℚ
centeredEnergySum (x ∷ y ∷ xs) =
  centeredFaceEnergy x y + centeredEnergySum (y ∷ xs)
centeredEnergySum _ = 0ℚ

firstSquare : List ℚ → ℚ
firstSquare [] = 0ℚ
firstSquare (x ∷ _) = square x

lastSquare : List ℚ → ℚ
lastSquare [] = 0ℚ
lastSquare (x ∷ []) = square x
lastSquare (x ∷ y ∷ xs) = lastSquare (y ∷ xs)

centeredSBP2FiniteTelescope :
  (xs : List ℚ) →
  centeredEnergySum xs
    ≡ half * (lastSquare xs + - firstSquare xs)
centeredSBP2FiniteTelescope [] = solve []
centeredSBP2FiniteTelescope (x ∷ []) = solve []
centeredSBP2FiniteTelescope (x ∷ y ∷ xs)
  rewrite centeredSBP2FiniteTelescope (y ∷ xs)
    | centeredFaceEnergyIdentity x y = solve []

-- The complete unweighted-normal characteristic boundary flux plus
-- the ACTUAL lower M SAT and upper P SAT. dy cancels the 1/dy
-- penalties with the endpoint H_00=H_NN=dy/2.
normalFluxAndSAT :
  ℚ → ℚ → ℚ → ℚ → ℚ → ℚ → ℚ
normalFluxAndSAT v p0 m0 pN mN target =
  half * (1ℚ + v) * (square pN + - square p0)
  + half * (v + - 1ℚ) * (square mN + - square m0)
  + (1ℚ + - v) * m0 * (target + - m0)
  + - ((1ℚ + v) * square pN)

completedNormalBoundary :
  ℚ → ℚ → ℚ → ℚ → ℚ → ℚ → ℚ
completedNormalBoundary v p0 m0 pN mN target =
  - (half * (1ℚ + v) * (square p0 + square pN))
  + - (half * (1ℚ + - v)
      * (square mN + square (m0 + - target)))
  + half * (1ℚ + - v) * square target

originalMovingSBP2SATBoundaryIdentity :
  (v p0 m0 pN mN target : ℚ) →
  normalFluxAndSAT v p0 m0 pN mN target
    ≡ completedNormalBoundary v p0 m0 pN mN target
originalMovingSBP2SATBoundaryIdentity v p0 m0 pN mN target
  = solve []

-- At t=4/3, v=-3/5, same original Israel SAT target.
sourceAtSlice : ℚ → ℚ → ℚ
sourceAtSlice p s = ((+ 1) / 4) * p + - (((+ 5) / 4) * s)

lowerBoundaryAtSlice : ℚ → ℚ → ℚ → ℚ
lowerBoundaryAtSlice p m s =
  - (((+ 1) / 5) * square p)
  + ((+ 4) / 5) * square m
  + ((+ 8) / 5) * m * (sourceAtSlice p s + - m)

completedLowerSourceAtSlice : ℚ → ℚ → ℚ → ℚ
completedLowerSourceAtSlice p m s =
  - (((+ 4) / 5) * square (m + - sourceAtSlice p s))
  + - (((+ 3) / 20) * square (p + ((+ 5) / 3) * s))
  + ((+ 5) / 3) * square s

originalMovingIsraelSourceCompletedSquare :
  (p m s : ℚ) →
  lowerBoundaryAtSlice p m s
    ≡ completedLowerSourceAtSlice p m s
originalMovingIsraelSourceCompletedSquare p m s = solve []

-- Total upper characteristic energy at original slice remains
-- -P_N^2/5 -4M_N^2/5. This is dissipation, not an energy
-- injection from the original outer SAT closure.
upperBoundaryAtSlice : ℚ → ℚ → ℚ
upperBoundaryAtSlice pN mN =
  - (((+ 1) / 5) * square pN)
  + - (((+ 4) / 5) * square mN)

originalFullNormalSourceBudgetAtSlice :
  (p0 m0 pN mN s : ℚ) →
  normalFluxAndSAT (- ((+ 3) / 5))
    p0 m0 pN mN (sourceAtSlice p0 s)
  ≡ completedLowerSourceAtSlice p0 m0 s
    + upperBoundaryAtSlice pN mN
originalFullNormalSourceBudgetAtSlice p0 m0 pN mN s
  = solve []

-- The original U stage includes the moving shift:
-- U_T=(P+M)/2, Udot=(P+M)/2 +v*(P-M)/2.
-- Under the exact scalar FV face Green formula, the radial force
-- cancels the derivative of radial-gradient energy only up to the
-- moving-coordinate shift. This explicit residual must be retained
-- in the full coupled energy budget, not called numerical leakage.

originalRadialGradientMovingShift :
  (conductance uLeft uRight pLeft pRight mLeft mRight v : ℚ) →
  (conductance * (uRight + - uLeft) *
    ((1ℚ + v) * (pRight + - pLeft)
       + (1ℚ + - v) * (mRight + - mLeft)))
  + - (conductance * (uRight + - uLeft) *
    ((pRight + - pLeft) + (mRight + - mLeft)))
  ≡ conductance * v * (uRight + - uLeft)
      * ((pRight + - pLeft) + - (mRight + - mLeft))
originalRadialGradientMovingShift
  conductance uLeft uRight pLeft pRight mLeft mRight v = solve []

-- Warp force remains nonzero in the bulk:
-- F_warp=-(3/2) invz*(P-M). Its contribution to the conventional
-- (P²+M²)/4 energy is -(3/4) invz*(P²-M²).
-- A z^-3 weighted energy and time-dependent Jacobian are required
-- to absorb/control it. This finite identity keeps the term visible.
originalWarpPowerInCharacteristicEnergy :
  (p m invz : ℚ) →
  half * (p + m)
    * (- (((+ 3) / 2) * invz * (p + - m)))
  ≡ - (((+ 3) / 4) * invz * (square p + - square m))
originalWarpPowerInCharacteristicEnergy p m invz = solve []
