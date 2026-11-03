{-# OPTIONS --safe #-}
module DASHI.Analysis.BishopMachinFirstPositiveSineZeroFromNativePhaseExact where

------------------------------------------------------------------------
-- K05-PI NATIVE BISHOP FIRST-POSITIVE-SINE-ZERO MIN-CUT.
--
-- The original source real pi_M = 16 atan_B(1/5) - 4 atan_B(1/239)
-- is proved positive by the rational Machin window.
--
-- One source-native pure-imaginary exponential Cauchy product AND
-- the original quarter-angle atan/tangent equality establish the
-- same-series sine zero at pi_M. If sine is strictly positive between
-- 0 and pi_M, no earlier positive zero can exist constructively.
--
-- The bounded-interval sine-sign theorem is a precise remaining
-- analytic obligation. The other two premises are the SAME existing
-- K05-PRODUCT and quarter-angle lemmas, not new assumptions.
--
-- Do NOT infer a least positive period from a first sine zero, and
-- do NOT promote Lean/Mathlib's pi proof into Agda without proof import.
--
-- Original authors: Machin, Bishop/Bridges, Murray, Csimma, and
-- prior DASHI signed-factorial and rational-window theorem owners.
-- Source-written; Agda kernel pending.
------------------------------------------------------------------------

open import Data.Empty using (⊥)
open import Data.Rational.Unnormalised as Q using (0ℚᵘ)
import Data.Rational.Unnormalised.Properties as QP
import Real as R
import RealProperties as RP

import DASHI.Foundations.BishopMachinArctanConstructionExact as Machin
import DASHI.Foundations.BishopMachinPiRationalWindowExact as Window
import DASHI.Analysis.BishopMachinQuarterPhaseQuadruplicationAlgebraExact as Quad
import DASHI.Analysis.BishopRound11ImaginaryProductPythagoreanReuseExact as Product
import DASHI.Physics.YangMills.YangMillsSubmissionRound11ExactCutset as Round11

sourceMachinPiStrictPositive :
  R._<_ R.0ℝ Machin.bishopMachinPi
sourceMachinPiStrictPositive =
  RP.<-trans
    (RP.p<q⇒p⋆<q⋆
      Q.0ℚᵘ Window.three
      (QP.positive⁻¹ Window.three))
    Window.threeBelowMachinPi

-- Strict positivity of the ACTUAL Bishop sine power-series over the
-- entire (0,pi_M) interval is the irreducible remaining sign theorem.
NativeSinePositiveBeforeMachinPi :
  Round11.Round11BishopCutset → Set
NativeSinePositiveBeforeMachinPi inputs =
  (x : R.ℝ) →
  R._<_ R.0ℝ x →
  R._<_ x Machin.bishopMachinPi →
  R._<_ R.0ℝ (Product.sinB inputs x)

record SourceMachinFirstPositiveSineZero
    (inputs : Round11.Round11BishopCutset) : Set where
  constructor source-machin-first-positive-sine-zero
  field
    piPositive : R._<_ R.0ℝ Machin.bishopMachinPi
    sineAtPiZero :
      R._≃_ (Product.sinB inputs Machin.bishopMachinPi) R.0ℝ
    noEarlierPositiveSineZero :
      (x : R.ℝ) →
      R._<_ R.0ℝ x →
      R._<_ x Machin.bishopMachinPi →
      R._≃_ (Product.sinB inputs x) R.0ℝ →
      ⊥

open SourceMachinFirstPositiveSineZero public

nativeSineNoPriorZero :
  (inputs : Round11.Round11BishopCutset) →
  NativeSinePositiveBeforeMachinPi inputs →
  (x : R.ℝ) →
  R._<_ R.0ℝ x →
  R._<_ x Machin.bishopMachinPi →
  R._≃_ (Product.sinB inputs x) R.0ℝ →
  ⊥
nativeSineNoPriorZero inputs sinePositive x xPositive xBeforePi sinZero =
  let
    strictlyPositive :
      R._<_ R.0ℝ (Product.sinB inputs x)
    strictlyPositive =
      sinePositive x xPositive xBeforePi

    impossible :
      R._<_ R.0ℝ R.0ℝ
    impossible =
      RP.<-respʳ-≃ sinZero strictlyPositive
  in
  RP.<-irrefl RP.≃-refl impossible

sourceMachinFirstSineZeroFromNativePhase :
  (inputs : Round11.Round11BishopCutset) →
  Product.Round11ImaginaryExpMultiplicative inputs →
  R._≃_ (Quad.quarterCos inputs) (Quad.quarterSin inputs) →
  NativeSinePositiveBeforeMachinPi inputs →
  SourceMachinFirstPositiveSineZero inputs
sourceMachinFirstSineZeroFromNativePhase
    inputs imaginaryProduct quarterEquality sinePositive =
  source-machin-first-positive-sine-zero
    sourceMachinPiStrictPositive
    (Data.Product.Base.proj₁
      (Product.round11MachinTrigEndpointFromImaginaryProduct
        inputs imaginaryProduct quarterEquality))
    (nativeSineNoPriorZero inputs sinePositive)
