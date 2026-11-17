module DASHI.Physics.Gravity.KSW668F8OriginalElectricWeylDefectSliceExact where

------------------------------------------------------------------------
-- XXIX original geometry G1/G2 geometric-vs-SMS Weyl defect identity.
-- Original Poincare AdS5 + moving a=t brane at t=4/3.
-- One local Cartesian TT polarization (H_yy=H,H_ww=-H).
-- The original normal is (-9/16,15/16), the brane tangent
-- (15/16,-9/16). No PDE or Neumann equation is assumed ZERO.
--
-- Define A=H_TT, B=H_xx, C=H_zz, D=H_Tz, X=H_T, Y=H_z.
-- The same-metric electric normal Weyl and source-free-region SMS
-- *expressions* satisfy for ARBITRARY rational jets:
--   E_electric - E_SMS = -(41/40) R_N -(3/16) R_bulk
--   R_N=(-9 X+15 Y)/16
--   R_bulk=-A+B+C-4Y.
-- This is the rational original-slice specialization of the verified
-- analytic arbitrary-positive-t identity
--   E_electric-E_SMS =
--     -(2t²+1)/(2t sqrt(1+t²))*R_N - R_bulk/(3t²).
--
-- For original SAT characteristic variables P=H_T+H_z, M=H_T-H_z,
-- and original target=-5/4 amp*S+1/4 P,
--   E_electric - E_SMS =
--       -123/128 amp*S +123/160 (M-target) -3/16 R_bulk.
-- For a source-free receiver amp*S=0.
--
-- This is an exact finite rational identity, not a uniform pointwise
-- estimate from an L2-in-time wall residual, nor a tensor-gauge proof
-- for the entire ell=0,2,4 wavepacket.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base using (ℚ; _+_; _*_; -_; _/_)
open import Data.Rational.Tactic.RingSolver using (solve)
import DASHI.Physics.Gravity.KSW668F8LinearElectricWeylPolarizationSliceExact as Electric
import DASHI.Physics.Gravity.KSW668F8WeakIsraelSATSliceExact as Wall

braneHdot : ℚ → ℚ → ℚ
braneHdot x y =
  ((+ 15) / 16) * x + - (((+ 9) / 16) * y)

braneHddot : ℚ → ℚ → ℚ → ℚ → ℚ → ℚ
braneHddot a c d x y =
  ((+ 225) / 256) * a
    + - (((+ 270) / 256) * d)
    + ((+ 81) / 256) * c
    + - (((+ 153) / 160) * x)
    + ((+ 27) / 32) * y

smsAtOriginalSlice : ℚ → ℚ → ℚ → ℚ → ℚ → ℚ → ℚ
smsAtOriginalSlice a b c d x y =
  - (((+ 1) / 2) * braneHddot a c d x y)
    + - (((+ 9) / 8) * braneHdot x y)
    + ((+ 9) / 32) * b

normalResidualAtOriginalSlice : ℚ → ℚ → ℚ
normalResidualAtOriginalSlice x y =
  - (((+ 9) / 16) * x)
    + ((+ 15) / 16) * y

bulkResidualAtOriginalSlice : ℚ → ℚ → ℚ → ℚ → ℚ
bulkResidualAtOriginalSlice a b c y =
  - a + b + c + - (((+ 4) / 1) * y)

originalWeylSMSResidualIdentity :
  (a b c d x y : ℚ) →
  Electric.electricNormalAtOriginalSlice a b c d
    + - smsAtOriginalSlice a b c d x y
    ≡ - (((+ 41) / 40) * normalResidualAtOriginalSlice x y)
      + - (((+ 3) / 16) * bulkResidualAtOriginalSlice a b c y)
originalWeylSMSResidualIdentity a b c d x y = solve []

characteristicH_T : ℚ → ℚ → ℚ
characteristicH_T p m = ((+ 1) / 2) * (p + m)

characteristicH_z : ℚ → ℚ → ℚ
characteristicH_z p m = ((+ 1) / 2) * (p + - m)

originalNormalResidualFromSAT :
  (amp src p m : ℚ) →
  normalResidualAtOriginalSlice
    (characteristicH_T p m) (characteristicH_z p m)
    ≡ ((+ 15) / 16) * amp * src
      + - (((+ 3) / 4) *
          (m + - Wall.weakIsraelTarget amp src p))
originalNormalResidualFromSAT amp src p m = solve []

originalWeylDefectFromSAT :
  (a b c d amp src p m : ℚ) →
  Electric.electricNormalAtOriginalSlice a b c d
    + - smsAtOriginalSlice
      a b c d (characteristicH_T p m) (characteristicH_z p m)
  ≡ - (((+ 123) / 128) * amp * src)
    + ((+ 123) / 160) * (m + - Wall.weakIsraelTarget amp src p)
    + - (((+ 3) / 16) *
      bulkResidualAtOriginalSlice a b c (characteristicH_z p m))
originalWeylDefectFromSAT a b c d amp src p m = solve []
