{-# OPTIONS --safe #-}
module DASHI.Analysis.BishopSquareZeroReflectsSetoidZeroExact where

------------------------------------------------------------------------
-- K05-PI CRITICAL MAX-CUT: NATIVE BISHOP SQUARE-ZERO CANCELLATION.
--
-- Reuse the ORIGINAL real absolute-value square identity, constructive
-- nonnegative square-order reflection and absolute-zero reflection.
-- This makes the mathematically necessary implication
--
--       x*x ~= 0  ==>  x ~= 0
--
-- a same-carrier theorem with NO arbitrary square-root function,
-- no classical field axiom, no excluded middle, and no replacement
-- completion or propositional quotient.
--
-- Original owners:
--   BishopComplexNormSquarePowerEnvelopeExact.absoluteSquare
--   BishopNonnegativeSquareReflectionExact.squareReflectsOnNonnegative
--   BalabanP33BishopChordMetricSeparationExact.absoluteZeroImpliesZero
-- Pinned semantics: vendor/bishop Real._≃_ and RealProperties.
------------------------------------------------------------------------

import Real as R
import RealProperties as RP

import DASHI.Analysis.BishopComplexNormSquarePowerEnvelopeExact as Norm
import DASHI.Foundations.BishopNonnegativeSquareReflectionExact as Reflect
import DASHI.Physics.YangMills.BalabanP33BishopChordMetricSeparationExact as Chord

squareZeroReflectsSetoidZero :
  (x : R.ℝ) →
  R._≃_ (R._*_ x x) R.0ℝ →
  R._≃_ x R.0ℝ
squareZeroReflectsSetoidZero x squaredZero =
  let
    absSquaredZero :
      R._≃_ (Norm.square (R.∣ x ∣)) R.0ℝ
    absSquaredZero =
      RP.≃-trans (Norm.absoluteSquare x) squaredZero

    absSquaredBelowZeroSquared :
      R._≤_
        (Norm.square (R.∣ x ∣))
        (Norm.square R.0ℝ)
    absSquaredBelowZeroSquared =
      RP.≤-respˡ-≃
        (RP.≃-symm absSquaredZero)
        (RP.≤-respʳ-≃
          (RP.≃-symm Chord.zeroSquare)
          (RP.≤-refl {x = R.0ℝ}))

    absBelowZero : R._≤_ (R.∣ x ∣) R.0ℝ
    absBelowZero =
      Reflect.squareReflectsOnNonnegative
        (RP.nonNeg∣x∣ x)
        RP.nonNeg0
        absSquaredBelowZeroSquared

    absoluteZero : R._≃_ (R.∣ x ∣) R.0ℝ
    absoluteZero =
      RP.≤-antisym absBelowZero
        (RP.nonNegx⇒0≤x (RP.nonNeg∣x∣ x))
  in
  Chord.absoluteZeroImpliesZero x absoluteZero
