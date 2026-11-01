module DASHI.Foundations.BishopErdosMachinConstantPositiveExact where

------------------------------------------------------------------------
-- STRICT POSITIVITY OF THE CONSTRUCTED ERDOS CONSTANT
--
-- The constant
--
--   c = pi_M * sqrt(2/3)
--
-- already exists in BishopSqrtTwoThirdsMachinConstantExact.  This owner adds
-- only the strict-positivity receipt needed by the partition residual kernel.
------------------------------------------------------------------------

open import Data.Integer.Base using (+_)
open import Data.Nat.Base using (z≤n; s≤s)
open import Data.Rational.Unnormalised as ℚ using (0ℚᵘ; _/_)
import Data.Rational.Unnormalised.Properties as ℚP

import Real as BishopReal
import RealProperties as BishopP

import DASHI.Foundations.BishopSqrtTwoThirdsMachinConstantExact as Constant
import DASHI.Foundations.BishopNatSquareRootPositiveExact as RootPositive
open import DASHI.Physics.YangMills.CompactLieProofLevel

oneThirdPositive : BishopReal.Positive (Constant.embed Constant.oneThird)
oneThirdPositive =
  BishopP.0<x⇒posx
    (BishopP.p<q⇒p⋆<q⋆
      0ℚᵘ Constant.oneThird
      (ℚP.positive⁻¹ Constant.oneThird))

sqrtSixPositive : BishopReal.Positive Constant.sqrtSix
sqrtSixPositive =
  RootPositive.canonicalFloorSquareRootPositive
    (s≤s z≤n)

sqrtTwoThirdsPositive : BishopReal.Positive Constant.sqrtTwoThirds
sqrtTwoThirdsPositive =
  BishopP.posx,y⇒posx*y oneThirdPositive sqrtSixPositive

erdosMachinConstantPositive : BishopReal.Positive Constant.erdosMachinConstant
erdosMachinConstantPositive =
  BishopP.posx,y⇒posx*y
    (BishopP.0<x⇒posx Constant.machinPiPositive)
    sqrtTwoThirdsPositive

erdosMachinConstantStrictlyPositive :
  BishopReal._<_ BishopReal.0ℝ Constant.erdosMachinConstant
erdosMachinConstantStrictlyPositive =
  BishopP.posx⇒0<x erdosMachinConstantPositive

bishopErdosMachinConstantPositiveLevel : ProofLevel
bishopErdosMachinConstantPositiveLevel = machineChecked
