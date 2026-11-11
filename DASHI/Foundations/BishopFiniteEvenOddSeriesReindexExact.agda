module DASHI.Foundations.BishopFiniteEvenOddSeriesReindexExact where

------------------------------------------------------------------------
-- ORIGINAL BISHOP REAL FINITE EVEN/ODD SERIES REINDEXING.
--
-- For ANY sequence f on the actual Bishop real carrier,
--
--   sum_{k<2N} f(k)
--     ~= sum_{k<N} f(2k) + sum_{k<N} f(2k+1).
--
-- Uses the SAME evenExponent and oddExponent as the repository's
-- configured original Bishop sine/cosine factorial source.
-- The identity is finite, all-N, nonparametric; no Cauchy limit
-- or summability assumption is smuggled in here.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong)
open import Data.Rational.Unnormalised using (0ℚᵘ)

import Real as BishopReal
import RealProperties as BishopP
import DASHI.Physics.YangMills.BalabanClayGate4BishopHalfRadiusRealEstimatesExact as Estimates

evenTerms : (Nat → BishopReal.ℝ) → Nat → BishopReal.ℝ
evenTerms f n = f (Estimates.evenExponent n)

oddTerms : (Nat → BishopReal.ℝ) → Nat → BishopReal.ℝ
oddTerms f n = f (Estimates.oddExponent n)

oddExponentIsSuccessorEven :
  ∀ n →
  Estimates.oddExponent n ≡ suc (Estimates.evenExponent n)
oddExponentIsSuccessorEven zero = refl
oddExponentIsSuccessorEven (suc n) =
  cong suc (cong suc (oddExponentIsSuccessorEven n))

originalBishopFiniteEvenOddSumReindex :
  (f : Nat → BishopReal.ℝ) →
  ∀ n →
  BishopReal._≃_
    (BishopReal.∑₀ f (Estimates.evenExponent n))
    (BishopReal._+_
      (BishopReal.∑₀ (evenTerms f) n)
      (BishopReal.∑₀ (oddTerms f) n))
originalBishopFiniteEvenOddSumReindex f zero =
  let open BishopP.ℝ-Solver in
  solve 0 (Κ 0ℚᵘ ⊜ Κ 0ℚᵘ ⊕ Κ 0ℚᵘ)
    BishopP.≃-refl
originalBishopFiniteEvenOddSumReindex f (suc n)
  rewrite oddExponentIsSuccessorEven n =
  let
    e = BishopReal.∑₀ (evenTerms f) n
    o = BishopReal.∑₀ (oddTerms f) n
    a = f (Estimates.evenExponent n)
    b = f (suc (Estimates.evenExponent n))
    previous = originalBishopFiniteEvenOddSumReindex f n
    substituted =
      BishopP.+-cong
        (BishopP.+-cong previous BishopP.≃-refl)
        BishopP.≃-refl
    regroup :
      BishopReal._≃_
        (BishopReal._+_ (BishopReal._+_ (BishopReal._+_ e o) a) b)
        (BishopReal._+_
          (BishopReal._+_ e a)
          (BishopReal._+_ o b))
    regroup =
      let open BishopP.ℝ-Solver in
      solve 4
        (λ e′ o′ a′ b′ →
          ((e′ ⊕ o′) ⊕ a′) ⊕ b′
          ⊜ (e′ ⊕ a′) ⊕ (o′ ⊕ b′))
        BishopP.≃-refl e o a b
  in
  BishopP.≃-trans substituted regroup
