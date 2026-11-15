module DASHI.Physics.Gravity.KSW668AdS5MovingNeumannCharacteristicRationalExact where

------------------------------------------------------------------------
-- Actual ORIGINAL moving a=t AdS5 tensor Neumann normal boundary,
-- not a Neumann-series inverse. On existing t=4/3 Einstein-Israel
-- rational slice, v=-3/5. For q+=H_T+H_z, q-=H_T-H_z,
-- g=[(1+v)q+ +(v-1)q-]/2, hence q-=q+/4 -5g/4.
-- The continuum real-square-root/retarded FIO remains OPEN in Agda.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_; -_; _/_)
open import Data.Rational.Tactic.RingSolver using (solve)

originalSliceT : ℚ
originalSliceT = (+ 4) / 3

originalWallVelocity : ℚ
originalWallVelocity = - ((+ 3) / 5)

originalReflection : ℚ
originalReflection = (+ 1) / 4

originalSourceFactor : ℚ
originalSourceFactor = - ((+ 5) / 4)

originalReflectionIdentity :
  (1ℚ + originalWallVelocity)
    ≡ (1ℚ + - originalWallVelocity) * originalReflection
originalReflectionIdentity = solve []

originalHomogeneousNeumannReflection :
  ((+ 2) / 5) * ((+ 1) / 8)
    + - (((+ 8) / 5) * ((+ 1) / 32))
    ≡ 0ℚ
originalHomogeneousNeumannReflection = solve []

sourceG : ℚ
sourceG = (+ 1) / 12

qOutgoing : ℚ
qOutgoing = (+ 1) / 8

qIncoming : ℚ
qIncoming = - ((+ 7) / 96)

originalForcedIncomingIsExact :
  qIncoming
    ≡ originalReflection * qOutgoing
      + originalSourceFactor * sourceG
originalForcedIncomingIsExact = solve []

originalFullNeumannNormalSource :
  (1ℚ + originalWallVelocity) * qOutgoing
    + (originalWallVelocity + - 1ℚ) * qIncoming
    ≡ ((+ 2) / 1) * sourceG
originalFullNeumannNormalSource = solve []
