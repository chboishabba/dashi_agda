module DASHI.Mathematics.Arithmetic.EisensteinJZeroCubicSymmetryValidation where

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Biology.EisensteinNineRingInterferenceExact as E
import DASHI.Mathematics.Arithmetic.EisensteinJZeroCubicSymmetryExact as CM

omegaCubeActsTriviallyOnX :
  CM.cube (E.multiply E.omega E.one) ≡ CM.cube E.one
omegaCubeActsTriviallyOnX = CM.omegaScaleCubeInvariant E.one

omegaSquaredCubeActsTriviallyOnX :
  CM.cube (E.multiply E.omegaSquared E.one) ≡ CM.cube E.one
omegaSquaredCubeActsTriviallyOnX = CM.omegaSquaredScaleCubeInvariant E.one

orderThreeXAction :
  CM.rotateX (CM.rotateX (CM.rotateX E.one)) ≡ E.one
orderThreeXAction = CM.rotateXThree E.one
