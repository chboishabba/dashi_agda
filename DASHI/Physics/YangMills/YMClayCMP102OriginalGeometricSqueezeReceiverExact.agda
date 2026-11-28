module DASHI.Physics.YangMills.YMClayCMP102OriginalGeometricSqueezeReceiverExact where

------------------------------------------------------------------------
-- CMP102 actual Bishop represented-real G_COUNT -> G source receiver.
-- Reuses the ORIGINAL finite-prefix values, original analytic limit
-- uniqueness and already-written master Bishop squeeze theorem.
-- All new bodies are source-written pending Agda 2.9 acceptance.
--
-- Final missing NATIVE SOURCE LEMMAS:
--  A. pointwise -3*(1/4)^n <= originalGPrefix X n <= 3*(1/4)^n
--     from original signed Cauchy coefficient cancellation and factorial
--     finite-sum majorants (all-degree mathematical certificate paid).
--  B. geometric bound sequence -> 0 in original Bishop Sequence.
-- This receiver neither assumes G(X)=0 nor invents a second series.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised using (_/_)
import Real as R
import RealProperties as P
import Sequence as Seq

import DASHI.Analysis.BishopSetoidSqueezeConvergenceExact as Squeeze
import DASHI.Physics.YangMills.BalabanBishopConcreteHalfBallSquareExact as Half
import DASHI.Physics.YangMills.YMClayCMP102OriginalGFiniteLimitTransportExact as Original

three : R.ℝ
three = R._⋆ (+ 3 / 1)

-- Exactly the original 3*4^(-count) geometric certificate.
originalGeometricRate : Nat → R.ℝ
originalGeometricRate count =
  R._*_ three (R.pow Half.bishopQuarter count)

-- Native use of the actual real-order bracket, not a bare numerical
-- exponential bound on an unrelated rational polynomial.
originalGPrefixZeroFromOriginalGeometricBracket :
  ∀ X →
  Seq._ConvergesTo_ originalGeometricRate R.0ℝ →
  (∀ count →
    R._≤_ (R.- (originalGeometricRate count))
      (Original.originalGPrefix X count)) →
  (∀ count →
    R._≤_ (Original.originalGPrefix X count)
      (originalGeometricRate count)) →
  Seq._ConvergesTo_ (Original.originalGPrefix X) R.0ℝ
originalGPrefixZeroFromOriginalGeometricBracket
  X rateZero lower upper =
  Squeeze.nativeBishopSqueeze
    (λ n → R.- (originalGeometricRate n))
    (Original.originalGPrefix X)
    originalGeometricRate
    R.0ℝ
    (Seq.xₙ→x∧x≃y⇒xₙ→y
      (Seq.-xₙ→-x₀ (R.0ℝ , rateZero))
      (P.≃-symm P.0≃-0))
    rateZero
    lower upper

-- SAME represented CMP109 series, SAME original G polynomial.
-- This closes the scalar CMP102 analytic zero as soon as A and B above
-- are constructed in the original Bishop order and Sequence kernel.
originalGZeroFromOriginalGeometricBracket :
  ∀ X (inside : R._≤_ (R.∣ X ∣) Half.bishopQuarter) →
  Seq._ConvergesTo_ originalGeometricRate R.0ℝ →
  (∀ count →
    R._≤_ (R.- (originalGeometricRate count))
      (Original.originalGPrefix X count)) →
  (∀ count →
    R._≤_ (Original.originalGPrefix X count)
      (originalGeometricRate count)) →
  R._≃_ (Original.originalG X inside) R.0ℝ
originalGZeroFromOriginalGeometricBracket
  X inside rateZero lower upper =
  Original.originalGZeroFromOriginalPrefixConvergence
    X inside
    (originalGPrefixZeroFromOriginalGeometricBracket
      X rateZero lower upper)
