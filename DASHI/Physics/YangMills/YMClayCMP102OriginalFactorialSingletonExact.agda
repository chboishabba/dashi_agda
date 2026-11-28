module DASHI.Physics.YangMills.YMClayCMP102OriginalFactorialSingletonExact where

------------------------------------------------------------------------
-- SOURCE singleton order owner (the first two A/B coefficients).
-- This consumes the EXISTING original factorial expression at n=0:
-- a0 = 1/(2!) = 1/2, b0 = 1/(3!) = 1/6.
-- Not a new coefficient sequence or a postulated initialization.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (zero)
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised using (_/_)
import Real as R
import RealProperties as P
import DASHI.Physics.YangMills.YMClayCMP102OriginalEndpointCauchyShiftExact as CMP102

originalASingleton : R._≃_
  (CMP102.aCoefficient zero) (R._⋆ (+ 1 / 2))
originalASingleton = P.≃-refl

originalBSingleton : R._≃_
  (CMP102.bCoefficient zero) (R._⋆ (+ 1 / 6))
originalBSingleton = P.≃-refl
