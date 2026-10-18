module DASHI.Mathematics.NumberTheory.FiniteDivisorPowerSumExact where

------------------------------------------------------------------------
-- EXECUTABLE FINITE DIVISOR POWER SUMS
--
-- DASHI CONTRIBUTION / REPO CROSS-POLLINATION
--
-- Reuse the already-owned positive-divisor scanner from
-- `FiniteDivisorSumExact` and the already-owned finite Nat fold.  No second
-- divisibility algorithm and no external/OEIS definition is introduced here.
--
--   sigma_k(n) = sum_{d | n, d>0} d^k
--
-- This owner is finite arithmetic only.  OEIS records are independent parity
-- coordinates; classical E4/E6 q-expansion authority is source-bound in a
-- separate owner.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Mathematics.NumberTheory.FiniteDivisorSumExact as Divisor
import DASHI.Mathematics.NumberTheory.FiniteWeightedReindexExact as Reindex
import DASHI.Moonshine.JInvariantEisensteinFiniteQSeriesExact as Series

powNat : Nat -> Nat -> Nat
powNat base zero = 1
powNat base (suc exponent) = base * powNat base exponent

sigmaPower : Nat -> Nat -> Nat
sigmaPower exponent n =
  Reindex.foldNat
    (λ d -> powNat d exponent)
    (Divisor.positiveDivisors n)

sigma3 : Nat -> Nat
sigma3 = sigmaPower 3

sigma5 : Nat -> Nat
sigma5 = sigmaPower 5

canonicalDivisorPowerKernel : Series.DivisorPowerKernel
canonicalDivisorPowerKernel =
  Series.divisor-power-kernel sigma3 sigma5

record FiniteDivisorPowerBoundary : Set where
  constructor finite-divisor-power-boundary
  field
    positiveDivisorScannerReused : Bool
    genericPowerFoldInternal : Bool
    sigma3Internal : Bool
    sigma5Internal : Bool
    eisensteinKernelInhabited : Bool
    oeisDefinesArithmetic : Bool
    modularFormAuthorityCreated : Bool
    analyticConvergenceCreated : Bool
    reading : String
open FiniteDivisorPowerBoundary public

canonicalFiniteDivisorPowerBoundary : FiniteDivisorPowerBoundary
canonicalFiniteDivisorPowerBoundary =
  finite-divisor-power-boundary
    true true true true true
    false false false
    "sigma3 and sigma5 are now executable from the repository's own positive-divisor enumeration; OEIS is parity-only and no finite arithmetic theorem creates modular-form or convergence authority"
