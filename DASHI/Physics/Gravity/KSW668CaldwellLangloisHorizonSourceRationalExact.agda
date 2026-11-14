module DASHI.Physics.Gravity.KSW668CaldwellLangloisHorizonSourceRationalExact where

------------------------------------------------------------------------
-- Original Caldwell-Langlois (2001) source Eq.(19),(20) rational algebra
-- benchmark. DOI 10.1016/S0370-2693(01)00631-1.
--
-- r_g^2 = (integral dt/a sqrt(1+ell^2 H^2))^2
--         - (integral dt/a ell*H)^2,
-- r_gamma = integral dt/a.
--
-- For two equal positive-weight source samples, choose rational
-- unit-hyperbola vectors at different H:
--   V0 = (1,0), V1 = (5/4,3/4).
-- Then I1=9/4, I2=3/4, I_gamma=2, and
--   r_g^2 = 9/2 = r_gamma^2 + 1/2 > r_gamma^2.
--
-- When BOTH samples have the SAME H represented by V1,
-- I1=5/2, I2=3/2 and r_g^2=4=r_gamma^2.
--
-- This is a finite 2-slice *source-equation algebra* benchmark,
-- not the full analytic inequality with integration or a physical
-- brane Einstein/Israel solution. The latter is numerically and
-- symbolically tested using the actual source formula by
-- scripts/ksw668_caldwell_langlois_original_eq19.py.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_; -_; _/_)
open import Data.Rational.Tactic.RingSolver using (solve)

variableHSourceI1 : ℚ
variableHSourceI1 = ((+ 9) / 4)

variableHSourceI2 : ℚ
variableHSourceI2 = ((+ 3) / 4)

twoSlicePhotonHorizon : ℚ
twoSlicePhotonHorizon = ((+ 2) / 1)

sourceVariableHGravityHorizonSquared : ℚ
sourceVariableHGravityHorizonSquared =
  (variableHSourceI1 * variableHSourceI1)
    + - (variableHSourceI2 * variableHSourceI2)

sourceVariableHStrictSquaredGap :
  sourceVariableHGravityHorizonSquared
    ≡ (twoSlicePhotonHorizon * twoSlicePhotonHorizon)
        + ((+ 1) / 2)
sourceVariableHStrictSquaredGap = solve []

constantHSourceI1 : ℚ
constantHSourceI1 = ((+ 5) / 2)

constantHSourceI2 : ℚ
constantHSourceI2 = ((+ 3) / 2)

sourceConstantHGravityHorizonSquared : ℚ
sourceConstantHGravityHorizonSquared =
  (constantHSourceI1 * constantHSourceI1)
    + - (constantHSourceI2 * constantHSourceI2)

sourceConstantHNoShortcut :
  sourceConstantHGravityHorizonSquared
    ≡ twoSlicePhotonHorizon * twoSlicePhotonHorizon
sourceConstantHNoShortcut = solve []

-- The reverse Minkowski/Cauchy identity behind the *full* original
-- integral inequality is purely polynomial for arbitrary rational x,y:
-- (1+x²)(1+y²)-(1+xy)²=(x-y)².
-- Inferring sqrt(1+x²)sqrt(1+y²)>=1+xy and integrating requires
-- a real ordered sqrt, measure/integration, nonnegative weight and
-- strictness control: not claimed as Agda-kernel complete here.

reverseMinkowskiQuadraticIdentity :
  (x y : ℚ) →
  (((1ℚ + (x * x)) * (1ℚ + (y * y)))
    + - ((1ℚ + (x * y)) * (1ℚ + (x * y))))
    ≡ (x + - y) * (x + - y)
reverseMinkowskiQuadraticIdentity x y = solve (x ∷ y ∷ [])
