module DASHI.Physics.Gravity.KSW668F8MovingWarpEnergyCancellationDefectExact where

------------------------------------------------------------------------
-- XXXIX: original moving AdS5 warp/normal energy SAME-OBJECT weld.
--
-- ORIGINAL coefficients from scripts/ksw668_f8_tt_multipole.py:
-- z(T,y)=b(T)+y, b(T)=1/t(T), b_T=v=-1/sqrt(1+t²),
-- w=z^-3, w_T=-3v*w/z.
-- P_T=(1+v) D_y P + (L_r U -3(P-M)/(2z)) + lower/upper SAT;
-- M_T=(v-1) D_y M + (L_r U -3(P-M)/(2z)) + SAT.
--
-- Use the CONSISTENT characteristic energy
-- E=1/2 sum H_i w_i (P_i²+M_i²).
-- Important normalization: its warp power is
-- -(3/2) sum H_i w_i/z_i (P_i²-M_i²),
-- NOT -(3/4) times that term, which belongs to 1/4 energy.
--
-- The continuum weighted normal transport term exactly cancels
-- moving weight derivative plus warp power, for arbitrary v:
-- +3/(2z)[(1+v)P²-(1-v)M²]
-- -3/(2z)[P²-M²]
-- -3v/(2z)[P²+M²] =0.
--
-- For the ACTUAL weighted SBP2 normal operator, the cancellation
-- leaves a precise discrete product-rule/quadrature residual:
--  (1+v)*(C_P -3/2 J_P) -(1-v)*(C_M -3/2 J_M)
-- C_X=1/2 sum_faces (w_i-w_{i+1})X_i X_{i+1},
-- J_X=sum_nodes H_i w_i/z_i X_i².
-- The full normal SAT boundary source squares of XXXVIII remain.
--
-- This is exact finite rational algebra, not a proof the defect is
-- bounded uniformly by moving PDE energy, nor SSPRK3 stability.
-- Pinned Agda kernel verification has NOT run.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base using (ℚ; 1ℚ; _+_; _*_; -_; _/_)
open import Data.Rational.Tactic.RingSolver using (solve)
import DASHI.Physics.Gravity.KSW668F8WarpWeightedSBP2CommutatorExact as SBP
import DASHI.Physics.Gravity.KSW668F8MovingSBP2SATBoundaryEnergyExact as Wall

half threeHalves : ℚ
half = (+ 1) / 2
threeHalves = (+ 3) / 2

sq : ℚ → ℚ
sq x = x * x

-- Actual characteristic energy convention E=1/2(P²+M²).
warpPower : ℚ → ℚ → ℚ → ℚ
warpPower invz p m =
  - (threeHalves * invz * (sq p + - sq m))

movingWeightPower : ℚ → ℚ → ℚ → ℚ → ℚ
movingWeightPower invz v p m =
  - (threeHalves * v * invz * (sq p + sq m))

continuumWeightedNormal : ℚ → ℚ → ℚ → ℚ → ℚ
continuumWeightedNormal invz v p m =
  threeHalves * invz *
    ((1ℚ + v) * sq p + - ((1ℚ + - v) * sq m))

originalWarpMovingContinuumBulkCancels :
  (invz v p m : ℚ) →
  continuumWeightedNormal invz v p m
    + warpPower invz p m
    + movingWeightPower invz v p m
  ≡ (+ 0) / 1
originalWarpMovingContinuumBulkCancels invz v p m = solve []

-- J_P and J_M are H_y-weighted sums of w/z times field squares.
-- C_P and C_M are weighted SBP2 face commutators, not divided by dy.
actualBulkWithoutRadial :
  ℚ → ℚ → ℚ → ℚ → ℚ → ℚ
actualBulkWithoutRadial v cP cM jP jM =
  (1ℚ + v) * cP + (v + - 1ℚ) * cM
  + - (threeHalves * (jP + - jM))
  + - (threeHalves * v * (jP + jM))

uncancelledDiscreteWarpDefect :
  ℚ → ℚ → ℚ → ℚ → ℚ → ℚ
uncancelledDiscreteWarpDefect v cP cM jP jM =
  (1ℚ + v) * (cP + - (threeHalves * jP))
  + - ((1ℚ + - v) * (cM + - (threeHalves * jM)))

originalMovingDiscreteBulkDefectExact :
  (v cP cM jP jM : ℚ) →
  actualBulkWithoutRadial v cP cM jP jM
  ≡ uncancelledDiscreteWarpDefect v cP cM jP jM
originalMovingDiscreteBulkDefectExact v cP cM jP jM = solve []

-- Exact face identity, producing a signed discrete derivative-square
-- defect and an explicit weighted quadrature mismatch.
faceCross : ℚ → ℚ → ℚ → ℚ → ℚ
faceCross wL wR xL xR =
  half * (wL + - wR) * xL * xR

faceMeanSquare : ℚ → ℚ → ℚ → ℚ → ℚ
faceMeanSquare wL wR xL xR =
  ((+ 1) / 4) * (wL + - wR) * (sq xL + sq xR)

faceJumpSquare : ℚ → ℚ → ℚ → ℚ → ℚ
faceJumpSquare wL wR xL xR =
  ((+ 1) / 4) * (wL + - wR) * sq (xR + - xL)

originalFaceDiscreteProductRuleDefect :
  (wL wR xL xR : ℚ) →
  faceCross wL wR xL xR
  ≡ faceMeanSquare wL wR xL xR
      + - (faceJumpSquare wL wR xL xR)
originalFaceDiscreteProductRuleDefect wL wR xL xR = solve []

-- Dimensionless t=dy/zLeft. For 0<=t<=1,
-- 9(1+t)^3-(3+3t+t²)^2
-- =t*(9+12t+2t²+t²*(1-t)) >=0.
-- This polynomial is a certificate for
-- (wLeft-wRight)/sqrt(wLeft*wRight) <= 3dy/zLeft
-- when zRight=zLeft+dy and dy<=zLeft.
-- The positivity/order step is not proved by this rational ring identity.
warpFaceEnvelopePolynomial :
  (t : ℚ) →
  ((+ 9) / 1) * (1ℚ + t) * (1ℚ + t) * (1ℚ + t)
  + - (((+ 3) / 1) + ((+ 3) / 1) * t + t * t)
      * (((+ 3) / 1) + ((+ 3) / 1) * t + t * t)
  ≡ t * (((+ 9) / 1) + ((+ 12) / 1) * t
            + ((+ 2) / 1) * t * t
            + t * t * (1ℚ + - t))
warpFaceEnvelopePolynomial t = solve []

-- General moving-Israel boundary source algebra, for ANY rational v.
-- a=1+v, b=1-v, original target relation
-- b*target=a*P-2*S (where S=amp*source).
-- This polynomial identity deliberately does NOT DIVIDE by v or b.
-- Under b*target=a*P-2S the last term is zero. For -1<v<0
-- the remaining squares give B_lower <= -S²/v.
-- The Agda rational ring theorem proves the certificate only;
-- positivity/order and inverse-v require separate acceptance.
lowerOriginalBoundary : ℚ → ℚ → ℚ → ℚ → ℚ
lowerOriginalBoundary v p m target =
  - (half * (1ℚ + v) * sq p)
  + - (half * (1ℚ + - v) * sq (m + - target))
  + half * (1ℚ + - v) * sq target

originalMovingSourcePolynomialCertificate :
  (v p m src target : ℚ) →
  let a = 1ℚ + v
      b = 1ℚ + - v
      targetDefect = b * target + - (a * p + - (((+ 2) / 1) * src))
      targetSum = b * target + (a * p + - (((+ 2) / 1) * src))
  in
  b * v * lowerOriginalBoundary v p m target
  ≡ a * sq (v * p + - src)
    + - (b * sq src)
    + - (half * b * b * v * sq (m + - target))
    + half * v * targetDefect * targetSum
originalMovingSourcePolynomialCertificate v p m src target = solve []

-- Same ORIGINAL moving brane at rational t=4/3: db/dt=-9/16,
-- dT/dt=15/16, v=-3/5, hence db/dt=v*(dT/dt).
-- General analytic identity requires the source calculus witnesses.
originalMovingBdotEqualsVelocityAtSlice :
  - ((+ 9) / 16)
  ≡ (- ((+ 3) / 5)) * ((+ 15) / 16)
originalMovingBdotEqualsVelocityAtSlice = solve []

-- For w=z^-3, z_T=v, the formal chain rule is
-- w_T=-3 v z^-4=-3 v w/z. Its incorporation into the
-- characteristic half-energy is exactly movingWeightPower above.
