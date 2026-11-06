{-# OPTIONS --safe #-}
module DASHI.Analysis.BishopSetoidSqueezeConvergenceExact where

------------------------------------------------------------------------
-- NATIVE BISHOP REAL SQUEEZE / ORDER LIMIT.
--
-- lowerₙ ≤ middleₙ ≤ upperₙ and convergence of both bounding
-- sequences to the SAME original Bishop real L imply middleₙ → L.
-- The finite inequalities are proof-relevant R._≤_; the analytic
-- output is the original Sequence._ConvergesTo_, not a new oracle.
--
-- K05 uses this with the positive triangle at index 2n between the
-- positive n-square and positive 2n-square rectangles.
--
-- Cauchy; Bishop and Bridges; Murray/Csimma pinned Bishop backend.
-- Source-written, exact-head kernel acceptance pending.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
import Real as R
import RealProperties as RP
import Sequence as S

import DASHI.Analysis.BishopVanishingDifferenceConvergenceExact as Vanish

squeezeError :
  (lower upper : Nat → R.ℝ) →
  (limit : R.ℝ) →
  S._ConvergesTo_ lower limit →
  S._ConvergesTo_ upper limit →
  S._ConvergesTo_
    (λ n → R._-_ (upper n) (lower n))
    R.0ℝ
squeezeError lower upper limit lowerConverges upperConverges =
  S.xₙ→x∧x≃y⇒xₙ→y
    (S.xₙ+yₙ→x₀+y₀
      (limit , upperConverges)
      (R.-_ limit ,
        S.-xₙ→-x₀ (limit , lowerConverges)))
    (RP.+-inverseʳ limit)

boundedDifference :
  (lower middle upper : Nat → R.ℝ) →
  (∀ n → R._≤_ (lower n) (middle n)) →
  (∀ n → R._≤_ (middle n) (upper n)) →
  ∀ n →
  R._≤_
    (R.∣ R._-_ (middle n) (lower n) ∣)
    (R.∣ R._-_ (upper n) (lower n) ∣)
boundedDifference lower middle upper lower≤middle middle≤upper n =
  let
    lower≤upper = RP.≤-trans (lower≤middle n) (middle≤upper n)
    difference1Nonnegative =
      RP.0≤x⇒nonNegx (RP.nonNegx⇒0≤x (lower≤middle n))
    difference2Nonnegative =
      RP.0≤x⇒nonNegx (RP.nonNegx⇒0≤x lower≤upper)
    absDifference1 = RP.nonNegx⇒∣x∣≃x difference1Nonnegative
    absDifference2 = RP.nonNegx⇒∣x∣≃x difference2Nonnegative
  in
  RP.≤-respˡ-≃ (RP.≃-symm absDifference1)
    (RP.≤-respʳ-≃ (RP.≃-symm absDifference2)
      (RP.+-monoˡ-≤ (R.-_ (lower n)) (middle≤upper n)))

nativeBishopSqueeze :
  (lower middle upper : Nat → R.ℝ) →
  (limit : R.ℝ) →
  S._ConvergesTo_ lower limit →
  S._ConvergesTo_ upper limit →
  (∀ n → R._≤_ (lower n) (middle n)) →
  (∀ n → R._≤_ (middle n) (upper n)) →
  S._ConvergesTo_ middle limit
nativeBishopSqueeze lower middle upper limit
    lowerConverges upperConverges lower≤middle middle≤upper =
  Vanish.vanishingDifferenceConvergence
    lowerConverges
    (squeezeError lower upper limit lowerConverges upperConverges)
    (boundedDifference lower middle upper lower≤middle middle≤upper)
