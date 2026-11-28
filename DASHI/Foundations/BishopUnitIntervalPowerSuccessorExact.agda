module DASHI.Foundations.BishopUnitIntervalPowerSuccessorExact where

------------------------------------------------------------------------
-- Section44: true original BISHOP power order, not Nat-only indices.
--
-- For any Bishop real 0<=u<=1, every successor power is no
-- larger than its predecessor. The original CMP102 signed input
-- is u=|X|<=1/4, supplied by its existing domain constructor.
--
-- This is the source-real analytic component of the two remaining
-- filtered Cauchy outer-wing majorants. The additional all-Nat
-- exponent transit and filtered positive Fin-rectangle comparison
-- are still distinct unpaid constructor welds.
--
-- Source-written, Agda 2.9 --safe elaboration pending.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; suc)
import Real as R
import RealProperties as P
import Sequence as Seq

bishopUnitIntervalPowerSuccessorAntitone :
  ∀ (u : R.ℝ) →
  R.NonNegative u →
  R._≤_ u R.1ℝ →
  ∀ n →
  R._≤_ (R.pow u (suc n)) (R.pow u n)
bishopUnitIntervalPowerSuccessorAntitone u uNN u≤one n =
  P.≤-respʳ-≃
    (P.*-identityʳ (R.pow u n))
    (P.*-monoʳ-≤-nonNeg
      u≤one
      (Seq.nonNegx⇒nonNegxⁿ n uNN))

------------------------------------------------------------------------
-- Zero-degree factor is already handled by the standard Bishop
-- power recursion; do not assume q>0 when X may be exactly zero.
------------------------------------------------------------------------
