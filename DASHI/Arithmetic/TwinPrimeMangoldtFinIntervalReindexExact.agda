module DASHI.Arithmetic.TwinPrimeMangoldtFinIntervalReindexExact where

------------------------------------------------------------------------
-- M13: ACTUAL FINITE INTERVAL REINDEXING (one whole 270 row).
--
-- Reuse original Sum.sumInterval, Rows.sumFinFrom and NatPeriod270.
-- A single indexed row retains ALL 270 residues, not just 27
-- sieve survivors. This is not a positivity or twin-prime theorem.
-- Source-written; kernel pending. 2026-10-29.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)
import Data.Fin.Base as Fin using (Fin; toℕ)
import Data.Nat.Properties as NP
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans; sym)

import DASHI.Arithmetic.TwinPrimeNat270PeriodResidualBidiExact as Period
import DASHI.Arithmetic.TwinPrimeResidualMangoldtBidiExact as Bidi
import DASHI.Arithmetic.TwinPrimeResidualMangoldtFiniteSumBidiExact as Sum
import DASHI.Arithmetic.TwinPrimeResidualMangoldtPeriodRowsExact as Rows

-- A finite-index interval whose values depend on the Nat index.
intervalFinSum : (S : Sum.AdditiveScalar) (f : Nat → Sum.Scalar S)
  (start count : Nat) → Sum.Scalar S
intervalFinSum S f start count =
  Rows.sumFinFrom S count (λ i → f (start + Fin.toℕ i))

-- No additive associativity or commutativity is required: the
-- two indexed folds visit the SAME ordered list of indices.
intervalFinSumExact :
  (S : Sum.AdditiveScalar) (f : Nat → Sum.Scalar S)
  (start count : Nat) →
  intervalFinSum S f start count ≡ Sum.sumInterval S f start count
intervalFinSumExact S f start zero =
  refl
intervalFinSumExact S f start (suc count) =
  cong₂ (Sum.add S)
    (cong f (NP.+-identityʳ start))
    (trans
      (Rows.sumFinCongruence S count
        (λ i → cong f
          (trans (NP.+-suc start (Fin.toℕ i))
                 refl)))
      (intervalFinSumExact S f (suc start) count))

-- The genuine rowNat uses residue FIRST in the addition. A Nat
-- commutativity proof is needed to identify it with the ordinary
-- ascending interval [270*k,270*k+270).
periodRowIsContiguousInterval :
  (S : Sum.AdditiveScalar) (f : Nat → Sum.Scalar S)
  (period : Nat) →
  Rows.periodRowSum S f period
    ≡ Sum.sumInterval S f (period * 270) 270
periodRowIsContiguousInterval S f period =
  trans
    (Rows.sumFinCongruence S 270
      (λ r → cong f
        (NP.+-comm (Fin.toℕ r) (period * 270))))
    (intervalFinSumExact S f (period * 270) 270)

-- Combining the two source owners gives an EXACT correlation BIDI
-- from the full 270-residue coded row into one ordinary interval.
periodCorrelationToContiguous :
  (S : Sum.AdditiveScalar)
  (C : Bidi.ArithmeticPairCorrelation (Sum.Scalar S))
  (period : Nat) →
  Rows.periodRowCodeSum S (Bidi.pairCorrelationAtPeriod C) period
    ≡ Sum.sumInterval S
        (Bidi.pairCorrelationAtNat C) (period * 270) 270
periodCorrelationToContiguous S C period =
  trans (Rows.periodPairCorrelationBidi S C period)
        (periodRowIsContiguousInterval S
          (Bidi.pairCorrelationAtNat C) period)

contiguousToPeriodCorrelation :
  (S : Sum.AdditiveScalar)
  (C : Bidi.ArithmeticPairCorrelation (Sum.Scalar S))
  (period : Nat) →
  Sum.sumInterval S (Bidi.pairCorrelationAtNat C)
    (period * 270) 270 ≡
  Rows.periodRowCodeSum S (Bidi.pairCorrelationAtPeriod C) period
contiguousToPeriodCorrelation S C period =
  sym (periodCorrelationToContiguous S C period)
