module DASHI.Physics.Gravity.KSW668F8LinearElectricWeylPolarizationSliceExact where

------------------------------------------------------------------------
-- Max-cut XXIX G1: local TT Cartesian polarization, exact moving-brane
-- normal-frame linearized electric-Weyl contraction at t=4/3.
--
-- ORIGINAL bulk in Poincare coordinates: g5=z^-2 eta5.
-- A simple transverse trace-free perturbation of the CONFORMAL metric:
--   h_yy=H(T,x,z), h_ww=-H(T,x,z), independent of y,w.
-- Flat first-variation Weyl pieces, using same sign convention as
-- R^a_bcd = d_c Gamma^a_bd - d_d Gamma^a_bc + ...:
--   C_yTyT = -H_TT/2 - boxH/6
--   C_yzyz = -H_zz/2 + boxH/6
--   C_yTyz = -H_Tz/2
--   boxH = -H_TT+H_xx+H_zz.
--
-- In the original brane orthonormal normal frame at t=4/3,
--   n^T=-9/16, n^z=15/16, e_y=z d_y.
-- By conformal covariance of Weyl, the orthonormal yy electric
-- projection uses these flat linearized C components:
--   E^electric_yy = nT² C_yTyT + 2 nT nz C_yTyz + nz² C_yzyz
--                 = -129/512 H_TT + 3/32 H_xx
--                   -177/512 H_zz + 135/256 H_Tz.
--
-- Independent full symbolic geometric derivation in max-cut XXIX
-- verify_linearized_electric_weyl.py. This Agda source proves the
-- rational contraction ONLY, not the differential-geometric first-
-- variation identity, and NOT the original solver's SMS E5 readout.
--
-- Crucial G1 remaining weld: impose actual bulk wave equation, moving
-- Israel boundary, source-free receiver, gauge, and original H tensor
-- angular reconstruction before identifying this with F8 E5.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base using (ℚ; _/_; _+_; _*_; -_)
open import Data.Rational.Tactic.RingSolver using (solve)

nT nZ : ℚ
nT = - ((+ 9) / 16)
nZ = (+ 15) / 16

boxH : ℚ → ℚ → ℚ → ℚ
boxH htt hxx hzz = - htt + hxx + hzz

linearWeylYTYT : ℚ → ℚ → ℚ → ℚ
linearWeylYTYT htt hxx hzz =
  - (((+ 1) / 2) * htt)
    + - (((+ 1) / 6) * boxH htt hxx hzz)

linearWeylYZYZ : ℚ → ℚ → ℚ → ℚ
linearWeylYZYZ htt hxx hzz =
  - (((+ 1) / 2) * hzz)
    + ((+ 1) / 6) * boxH htt hxx hzz

linearWeylYTYZ : ℚ → ℚ
linearWeylYTYZ htz = - (((+ 1) / 2) * htz)

electricNormalAtOriginalSlice : ℚ → ℚ → ℚ → ℚ → ℚ
electricNormalAtOriginalSlice htt hxx hzz htz =
  nT * nT * linearWeylYTYT htt hxx hzz
  + (((+ 2) / 1) * nT * nZ * linearWeylYTYZ htz)
  + nZ * nZ * linearWeylYZYZ htt hxx hzz

electricNormalExactCoefficients :
  (htt hxx hzz htz : ℚ) →
  electricNormalAtOriginalSlice htt hxx hzz htz
    ≡ - (((+ 129) / 512) * htt)
       + ((+ 3) / 32) * hxx
       + - (((+ 177) / 512) * hzz)
       + ((+ 135) / 256) * htz
electricNormalExactCoefficients htt hxx hzz htz = solve []

normalMinkowskiNormAtOriginalSlice :
  - (nT * nT) + nZ * nZ ≡ (+ 9) / 16
normalMinkowskiNormAtOriginalSlice = solve []

data LinearElectricWeylSourceIdentityHole : Set where
  conformalCovarianceDerivedFromCurvedConnection :
    LinearElectricWeylSourceIdentityHole
  originalTTWaveAndIsraelReduceNormalJets :
    LinearElectricWeylSourceIdentityHole
  SMSProjectedWeylIdentifiedWithNormalElectric :
    LinearElectricWeylSourceIdentityHole
