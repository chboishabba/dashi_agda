{-# OPTIONS --safe #-}
module DASHI.Analysis.BishopSquareZeroReflectsSetoidZeroExact where

------------------------------------------------------------------------
-- K05-PI: NATIVE BISHOP SQUARE-ZERO REFLECTION, SELF-CONTAINED.
--
-- Do NOT route this proof through the unrelated YM quaternion/chord
-- geometry. Reuse just the original vendored Real/RealProperties,
-- source |x|²=x² and constructive nonnegative square reflection.
--
--   x*x ~ 0 => |x|*|x| ~ 0 => |x| <= 0 => |x| ~ 0 => x ~ 0.
--
-- The final absolute-zero reflection is proved directly from
-- x<=|x| and -x<=|-x|, using Bishop order antisymmetry.
-- No square root backend, no external theorem, no new real carrier.
------------------------------------------------------------------------

open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised using (_/_)
import Real as R
import RealProperties as RP

import DASHI.Analysis.BishopComplexNormSquarePowerEnvelopeExact as Norm
import DASHI.Foundations.BishopNonnegativeSquareReflectionExact as Reflect

zeroSquare :
  R._≃_ (Norm.square R.0ℝ) R.0ℝ
zeroSquare =
  let open RP.ℝ-Solver in
  solve 0
    (Κ (+ 0 / 1) ⊗ Κ (+ 0 / 1) ⊜ Κ (+ 0 / 1))
    RP.≃-refl

nativeAbsoluteZeroImpliesZero :
  (x : R.ℝ) →
  R._≃_ (R.∣ x ∣) R.0ℝ →
  R._≃_ x R.0ℝ
nativeAbsoluteZeroImpliesZero x absoluteZero =
  let
    xBelowZero : R._≤_ x R.0ℝ
    xBelowZero =
      RP.≤-respʳ-≃ absoluteZero (RP.x≤∣x∣ {x = x})

    negXBelowZero : R._≤_ (R.-_ x) R.0ℝ
    negXBelowZero =
      RP.≤-respʳ-≃
        (RP.≃-trans
          (RP.∣-x∣≃∣x∣ {x = x})
          absoluteZero)
        (RP.x≤∣x∣ {x = R.-_ x})

    zeroBelowX : R._≤_ R.0ℝ x
    zeroBelowX =
      RP.≤-respʳ-≃
        (RP.neg-involutive x)
        (RP.≤-respˡ-≃
          RP.0≃-0
          (RP.neg-mono-≤ negXBelowZero))
  in
  RP.≤-antisym xBelowZero zeroBelowX

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
          (RP.≃-symm zeroSquare)
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
  nativeAbsoluteZeroImpliesZero x absoluteZero
