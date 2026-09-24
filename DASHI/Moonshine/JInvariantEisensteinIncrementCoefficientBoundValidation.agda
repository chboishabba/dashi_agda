module DASHI.Moonshine.JInvariantEisensteinIncrementCoefficientBoundValidation where

open import Agda.Builtin.Nat using (Nat; suc; _*_)
open import Data.Nat.Base using (_≤_)

import DASHI.Mathematics.NumberTheory.FiniteDivisorPowerSumExact as Divisor
import DASHI.Moonshine.JInvariantEisensteinIncrementCoefficientBoundExact as P

e4IncrementCoefficientRegression :
  (n : Nat) ->
  P.e4IncrementCoefficient n
  ≤ 240 * (Divisor.powNat (suc n) 3 * suc n)
e4IncrementCoefficientRegression = P.e4IncrementCoefficientBound

e6IncrementCoefficientRegression :
  (n : Nat) ->
  P.e6IncrementCoefficient n
  ≤ 504 * (Divisor.powNat (suc n) 5 * suc n)
e6IncrementCoefficientRegression = P.e6IncrementCoefficientBound
