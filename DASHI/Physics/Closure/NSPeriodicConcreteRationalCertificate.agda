module DASHI.Physics.Closure.NSPeriodicConcreteRationalCertificate where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

open import DASHI.Physics.Closure.NSCompactGammaConcreteDyadicScalarCertificate
  using (_≤ᴺ_; z≤n; s≤s)

------------------------------------------------------------------------
-- Exact common-denominator arithmetic for the finite R = 8 receipt.
--
-- A natural n denotes n/128.  These are finite-model constants only; this module
-- is not connected to the official analytic authority without a separate carrier
-- identification theorem.
------------------------------------------------------------------------

farLowAtEight128 farHighAtEight128 oneEighth128 : Nat
farLowAtEight128 = 1
farHighAtEight128 = 8
oneEighth128 = 16

farLowFitsOneEighth128 : farLowAtEight128 ≤ᴺ oneEighth128
farLowFitsOneEighth128 = s≤s z≤n

farHighFitsOneEighth128 : farHighAtEight128 ≤ᴺ oneEighth128
farHighFitsOneEighth128 =
  s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))

combinedTailAtEight128 : Nat
combinedTailAtEight128 = farLowAtEight128 + farHighAtEight128

combinedTailAtEightIsNine128 : combinedTailAtEight128 ≡ 9
combinedTailAtEightIsNine128 = refl

nearDeltaLowHigh16 nearDeltaHighLow16 nearDeltaHighHigh16 : Nat
nearDeltaLowHigh16 = 1
nearDeltaHighLow16 = 1
nearDeltaHighHigh16 = 2

nearDeltaTotal16 : Nat
nearDeltaTotal16 =
  nearDeltaLowHigh16 + nearDeltaHighLow16 + nearDeltaHighHigh16

nearDeltaTotalIsQuarter : nearDeltaTotal16 ≡ 4
nearDeltaTotalIsQuarter = refl

nearResidualCoefficient : Nat
nearResidualCoefficient = 64

nearResidualRegression : nearResidualCoefficient ≡ 64
nearResidualRegression = refl
