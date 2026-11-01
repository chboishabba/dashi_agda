module DASHI.Moonshine.JInvariantEisensteinIncrementCoefficientBoundExact where

------------------------------------------------------------------------
-- NATURAL COEFFICIENT ENVELOPES FOR THE LITERAL E4/E6 INCREMENTS
--
-- The truncation-increment owner exposes
--
--   240 sigma_3(n+1) q^(n+1)
--   504 sigma_5(n+1) q^(n+1).
--
-- The canonical internal divisor kernel already proves the finite arithmetic
-- bounds sigma_3(m) <= m^3*m and sigma_5(m) <= m^5*m.  This owner transports
-- those bounds through the exact 240/504 natural multipliers consumed by the
-- recurrence.  It remains finite Nat arithmetic: no complex modulus, q decay,
-- convergence, or analytic Eisenstein authority is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; suc; _*_)
open import Data.Nat.Base using (_≤_)
import Data.Nat.Properties as NatP

import DASHI.Mathematics.NumberTheory.FiniteDivisorPowerSumExact as Divisor
import DASHI.Moonshine.JInvariantEisensteinFiniteQSeriesExact as Series
import DASHI.Moonshine.JInvariantEisensteinInternalDivisorPowerKernelExact as Internal

e4IncrementCoefficient : Nat -> Nat
e4IncrementCoefficient n =
  240 * Series.sigma3 Internal.internalDivisorPowerKernel (suc n)

e6IncrementCoefficient : Nat -> Nat
e6IncrementCoefficient n =
  504 * Series.sigma5 Internal.internalDivisorPowerKernel (suc n)

e4IncrementCoefficientBound :
  (n : Nat) ->
  e4IncrementCoefficient n
  ≤ 240 * (Divisor.powNat (suc n) 3 * suc n)
e4IncrementCoefficientBound n =
  NatP.*-mono-≤
    NatP.≤-refl
    (Internal.internalSigma3QuarticBound (suc n))

e6IncrementCoefficientBound :
  (n : Nat) ->
  e6IncrementCoefficient n
  ≤ 504 * (Divisor.powNat (suc n) 5 * suc n)
e6IncrementCoefficientBound n =
  NatP.*-mono-≤
    NatP.≤-refl
    (Internal.internalSigma5SexticBound (suc n))
