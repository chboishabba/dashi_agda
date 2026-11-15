{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650Rational345LipschitzIntegralRound854Exact where

------------------------------------------------------------------------
-- NS R854: UNCONDITIONAL RATIONAL ARITHMETIC on the ORIGINAL 345 rate.
--
-- R850 independently identifies the source-selected initial rate
--   r0 = -28273644/125.
-- R828 independent REAL ODE study supplies the conservative claimed
-- rate-Lipschitz constant
--   L = 391309593930357307785216
-- and R830's exact time T.
--
-- Here we prove the exact scalar r0+L*T is already strictly below
-- the previous coarse R830 upper bound -226189/2, and the sharper
-- linearly integrated bound r0*T+(L*T*T)/2 is strictly negative.
--
-- This file DOES NOT construct a real-time physical R408 trajectory,
-- the true real Lipschitz lemma for that trajectory, or an original
-- same-object integral. Those remain the nontrivial R830/R853 leaves.
-- It is an arithmetic improvement, NOT Navier–Stokes regularity.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _*_; _/_; _+_; _<_)
import Data.Rational.Properties as ℚP
open import Relation.Nullary.Decidable.Core using (toWitness)

import DASHI.Physics.Closure.NSTriadKNR650Rational345SnapshotNormalizationRound829Exact as R829
import DASHI.Physics.Closure.NSTriadKNR650Rational345ShortTimeRound830Exact as R830

sourceLipschitzConstant854 : ℚ
sourceLipschitzConstant854 =
  (+ 391309593930357307785216) / 1

actualInitialSelectedRate854 : ℚ
actualInitialSelectedRate854 = R829.expectedRate345

exactHorizon854 : ℚ
exactHorizon854 = R830.shortTime345

linearlyTransportedRateUpper854 : ℚ
linearlyTransportedRateUpper854 =
  actualInitialSelectedRate854
    + (sourceLipschitzConstant854 * exactHorizon854)

linearlyTransportedRateStrictlyNegative854 :
  linearlyTransportedRateUpper854 < 0ℚ
linearlyTransportedRateStrictlyNegative854 =
  toWitness (ℚP._<?_ linearlyTransportedRateUpper854 0ℚ)

strongerThanExistingCoarseRateUpper854 :
  linearlyTransportedRateUpper854 < R830.rateUpper345
strongerThanExistingCoarseRateUpper854 =
  toWitness
    (ℚP._<?_ linearlyTransportedRateUpper854 R830.rateUpper345)

-- Integral of the affine upper envelope r0+L*t from 0 to T,
-- IF a real-time trajectory with that bound is later constructed.
-- The scalar expression is exact over the ORIGINAL rational constants.
affineIntegratedUpper854 : ℚ
affineIntegratedUpper854 =
  (actualInitialSelectedRate854 * exactHorizon854)
  + ((sourceLipschitzConstant854
        * exactHorizon854 * exactHorizon854)
      / 2)

affineIntegratedUpperStrictlyNegative854 :
  affineIntegratedUpper854 < 0ℚ
affineIntegratedUpperStrictlyNegative854 =
  toWitness (ℚP._<?_ affineIntegratedUpper854 0ℚ)

-- The exact conservative R830 integral upper bound is weaker.
affineIntegralSharperThanR830854 :
  affineIntegratedUpper854 < R830.integratedUpper345
affineIntegralSharperThanR830854 =
  toWitness
    (ℚP._<?_ affineIntegratedUpper854 R830.integratedUpper345)

round854ArithmeticBoundSourceWritten : Bool
round854ArithmeticBoundSourceWritten = true

round854RealODELipschitzTransportConstructed : Bool
round854RealODELipschitzTransportConstructed = false

round854OriginalR408RealTrajectoryConstructed : Bool
round854OriginalR408RealTrajectoryConstructed = false

round854ClayPromotion : Bool
round854ClayPromotion = false

round854NoClayPromotion :
  round854ClayPromotion ≡ false
round854NoClayPromotion = refl
