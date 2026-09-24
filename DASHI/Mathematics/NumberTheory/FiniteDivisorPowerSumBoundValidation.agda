module DASHI.Mathematics.NumberTheory.FiniteDivisorPowerSumBoundValidation where

open import Agda.Builtin.Nat using (Nat; _*_)
open import Data.Nat.Base using (_≤_)

import DASHI.Mathematics.NumberTheory.FiniteDivisorPowerSumExact as Power
import DASHI.Mathematics.NumberTheory.FiniteDivisorPowerSumBoundExact as P

------------------------------------------------------------------------
-- RED owner for the exact finite coefficient-growth payment.
------------------------------------------------------------------------

sigmaPowerPolynomialEnvelope :
  (exponent n : Nat) ->
  Power.sigmaPower exponent n ≤ Power.powNat n exponent * n
sigmaPowerPolynomialEnvelope = P.sigmaPowerPolynomialBound

sigma3QuarticEnvelope :
  (n : Nat) ->
  Power.sigma3 n ≤ Power.powNat n 3 * n
sigma3QuarticEnvelope = P.sigma3QuarticBound

sigma5SexticEnvelope :
  (n : Nat) ->
  Power.sigma5 n ≤ Power.powNat n 5 * n
sigma5SexticEnvelope = P.sigma5SexticBound
