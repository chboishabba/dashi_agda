module DASHI.Physics.Gravity.KSW668F8SourceFreeElectricWeylSMSSliceWeldExact where

------------------------------------------------------------------------
-- Max-cut XXIX G1 nontrivial same-object source-free geometric weld.
-- Original a=t brane at t=4/3, Poincare AdS5 z=3/4,
-- u=(15/16,-9/16), n=(-9/16,15/16) in (T,z).
-- One Cartesian TT polarization h_yy=H, h_ww=-H.
--
-- Bulk wave: -H_TT+H_xx+H_zz - 3/z H_z=0.
-- Original source-FREE moving Neumann at receiver: n.H=0.
-- Write A=H_TT, B=H_xx, E=dH/dt along brane; then H_z=E,
-- H_T=(5/3)E; bulk PDE gives
--   C=H_zz=A-B+4E.
-- Differentiate n.H=0 tangentially and use the PDE:
--   D=H_Tz=(15/17)A-(15/34)B+(118/85)E.
-- Induced acceleration:
--   H_ddot=(9/34)A+(81/544)B-(129/136)E.
--
-- With exact linearised 5D Weyl/electric normal projection reused:
-- E(normal)= -(129/512)A+(3/32)B-(177/512)C+(135/256)D.
-- SMS readout in source-free region, eta=ln t:
-- E_SMS=-(t² H_ddot+3t H_dot-H_xx)/(2t²).
-- At t=4/3 these two are IDENTICAL as rational functions.
--
-- The Agda proofs below are the finite rational reduction and ring
-- arithmetic. The differential geometry, PDE boundary differentiation,
-- general real t, and full angular TT reconstruction are independently
-- derived in SymPy and remain unimported Agda analytic obligations.
-- NOT a full G1 curvature/gauge theorem or physical detector.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; -_; _/_)
open import Data.Rational.Tactic.RingSolver using (solve)
import DASHI.Physics.Gravity.KSW668F8LinearElectricWeylPolarizationSliceExact as Electric

sourceFreeBulkZZ : ℚ → ℚ → ℚ → ℚ
sourceFreeBulkZZ a b e =
  a + - b + ((+ 4) / 1) * e

sourceFreeBulkTZ : ℚ → ℚ → ℚ → ℚ
sourceFreeBulkTZ a b e =
  ((+ 15) / 17) * a
    + - (((+ 15) / 34) * b)
    + ((+ 118) / 85) * e

sourceFreeBraneAcceleration : ℚ → ℚ → ℚ → ℚ
sourceFreeBraneAcceleration a b e =
  ((+ 9) / 34) * a
    + ((+ 81) / 544) * b
    + - (((+ 129) / 136) * e)

sourceFreeBulkTTWaveAtSlice :
  (a b e : ℚ) →
  - a + b + sourceFreeBulkZZ a b e
    + - (((+ 4) / 1) * e)
  ≡ 0ℚ
sourceFreeBulkTTWaveAtSlice a b e = solve []

-- Tangential derivative of (n.H)=0 in the physical moving frame:
-- -675(A+C)+1530 D +576 E=0, after multiplying denominators.
sourceFreeDifferentiatedMovingNeumannAtSlice :
  (a b e : ℚ) →
  - (((+ 675) / 1) * (a + sourceFreeBulkZZ a b e))
    + ((+ 1530) / 1) * sourceFreeBulkTZ a b e
    + ((+ 576) / 1) * e
  ≡ 0ℚ
sourceFreeDifferentiatedMovingNeumannAtSlice a b e = solve []

sourceFreeSMSAtOriginalSlice : ℚ → ℚ → ℚ → ℚ
sourceFreeSMSAtOriginalSlice a b e =
  - (((+ 1) / 2) * sourceFreeBraneAcceleration a b e)
    + - (((+ 9) / 8) * e)
    + ((+ 9) / 32) * b

sourceFreeElectricWeylEqualsSMSAtOriginalSlice :
  (a b e : ℚ) →
  Electric.electricNormalAtOriginalSlice
    a b (sourceFreeBulkZZ a b e) (sourceFreeBulkTZ a b e)
    ≡ sourceFreeSMSAtOriginalSlice a b e
sourceFreeElectricWeylEqualsSMSAtOriginalSlice a b e = solve []

sourceFreeSMSClosedForm :
  (a b e : ℚ) →
  sourceFreeSMSAtOriginalSlice a b e
    ≡ - (((+ 9) / 68) * a)
      + ((+ 225) / 1088) * b
      + - (((+ 177) / 272) * e)
sourceFreeSMSClosedForm a b e = solve []
