module DASHI.Arithmetic.TwinPrimeMangoldtPartialPeriodPartitionExact where

------------------------------------------------------------------------
-- M13: BOTH PARTIAL EDGE SEGMENTS + ARBITRARILY MANY COMPLETE PERIODS
--
-- Reuses MultiPeriodConcatExact's source-written all-block BIDI and
-- original Fin270 period codec. Given a witness that the initial
-- partial segment ends at a 270 boundary, precisely reassemble the
-- original contiguous interval. Every finite correlation term occurs
-- exactly once and in the SAME order. No Scalar commutativity.
--
-- This is a conditional-on-alignment FINITE identity, not a claim
-- that an analytic positive gap-two correlation has been proved.
-- Original number-theory, Pareto, Ibrahim and QID identity owners
-- retain their own proof authority. Source-written; kernel pending.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Arithmetic.TwinPrimeResidualMangoldtFiniteSumBidiExact as Sum
import DASHI.Arithmetic.TwinPrimeResidualMangoldtBidiExact as Bidi
import DASHI.Arithmetic.TwinPrimeMangoldtMultiPeriodConcatExact as Multi

partialPeriodPartition :
  (S : Sum.AdditiveScalar) (M : Multi.MonoidSum S)
  (C : Bidi.ArithmeticPairCorrelation (Sum.Scalar S))
  (start prefixLen period blocks suffixLen : Nat) →
  start + prefixLen ≡ period * 270 →
  Sum.sumInterval S (Bidi.pairCorrelationAtNat C)
    start (prefixLen + (blocks * 270 + suffixLen))
  ≡
  Sum.add S
    (Sum.sumInterval S (Bidi.pairCorrelationAtNat C) start prefixLen)
    (Sum.add S
      (Multi.codeBlockRows S C period blocks)
      (Sum.sumInterval S (Bidi.pairCorrelationAtNat C)
        (period * 270 + blocks * 270) suffixLen))
partialPeriodPartition S M C start prefixLen period blocks suffixLen aligned =
  trans
    (sym
      (Multi.sumIntervalSplit S M f start prefixLen
        (blocks * 270 + suffixLen)))
    (cong (Sum.add S (Sum.sumInterval S f start prefixLen))
      (trans
        (cong
          (λ idx → Sum.sumInterval S f idx
            (blocks * 270 + suffixLen))
          aligned)
        (trans
          (sym
            (Multi.sumIntervalSplit S M f
              (period * 270) (blocks * 270) suffixLen))
          (cong₂ (Sum.add S)
            (sym (Multi.codeBlockRowsToInterval S M C period blocks))
            refl))))
  where
    f : Nat → Sum.Scalar S
    f = Bidi.pairCorrelationAtNat C

partialPeriodPartitionBidi :
  (S : Sum.AdditiveScalar) (M : Multi.MonoidSum S)
  (C : Bidi.ArithmeticPairCorrelation (Sum.Scalar S))
  (start prefixLen period blocks suffixLen : Nat) →
  start + prefixLen ≡ period * 270 →
  Sum.add S
    (Sum.sumInterval S (Bidi.pairCorrelationAtNat C) start prefixLen)
    (Sum.add S
      (Multi.codeBlockRows S C period blocks)
      (Sum.sumInterval S (Bidi.pairCorrelationAtNat C)
        (period * 270 + blocks * 270) suffixLen))
  ≡
  Sum.sumInterval S (Bidi.pairCorrelationAtNat C)
    start (prefixLen + (blocks * 270 + suffixLen))
partialPeriodPartitionBidi S M C start prefixLen period blocks suffixLen
    aligned =
  sym (partialPeriodPartition S M C start prefixLen period blocks
    suffixLen aligned)
