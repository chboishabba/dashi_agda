module DASHI.Physics.YangMills.YMClayCMP102OriginalGFiniteLimitTransportExact where

------------------------------------------------------------------------
-- CMP102 P0: actual original CMP109 represented-series polynomial limit.
--
-- This proves that the ORIGINAL finite G_N expression converges to the
-- polynomial of the ORIGINAL represented Bishop CMP109 A/B limits.
-- It also reduces G(X) ~= 0 to the concrete still-open assertion that
-- those SAME finite G_N expressions converge to zero (the independent
-- quarter-radius 3*4^-N bound is currently a mathematical certificate).
--
-- No second power series, analytic carrier, convergence postulate or
-- Cauchy product theorem is introduced. All theorem bodies source-written;
-- NO Agda 2.9 kernel receipt. Source: Bałaban CMP102/109;
-- Bishop/Bridges, Murray/Csimma; original DASHI source coefficients.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Product using (_,_)
import Real as R
import RealProperties as P
import Sequence as Seq

import DASHI.Physics.YangMills.BalabanBishopConcreteHalfBallSquareExact as Half
import DASHI.Physics.YangMills.BalabanCMP109BishopRootFreeSeriesExact as CMP109
import DASHI.Physics.YangMills.YMClayCMP102OriginalEndpointCauchyShiftExact as CMP102
import DASHI.Physics.YangMills.YMClayCMP102OriginalCMP109BishopSeriesSameSourceBIDIExact as Same

-- Exactly the old CMP109 finite histories on CMP102's definitionally
-- equivalent coefficients, using the original Sequence.SeriesOf.
aPrefix bPrefix : R.ℝ → Nat → R.ℝ
aPrefix X n = Seq.SeriesOf (CMP109.term CMP102.aCoefficient X) n
bPrefix X n = Seq.SeriesOf (CMP109.term CMP102.bCoefficient X) n

constantConverges : (x : R.ℝ) → Seq._ConvergesTo_ (λ _ → x) x
constantConverges x = Seq.xₙ≃c⇒xₙ→c (λ {(suc _) → P.≃-refl})

sumConverges :
  ∀ {left right : Nat → R.ℝ} {x y : R.ℝ} →
  Seq._ConvergesTo_ left x →
  Seq._ConvergesTo_ right y →
  Seq._ConvergesTo_ (λ n → R._+_ (left n) (right n)) (R._+_ x y)
sumConverges {x = x} {y = y} leftConv rightConv =
  Seq.xₙ+yₙ→x₀+y₀ (x , leftConv) (y , rightConv)

-- The five terms of G_N = 1 - 2 A_N - X A_N² + 2X B_N + X² B_N².
negativeAPrefix negativeASquarePrefix positiveBPrefix positiveBSquarePrefix :
  R.ℝ → Nat → R.ℝ
negativeAPrefix X n = R.-_ (R._*_ CMP102.two (aPrefix X n))
negativeASquarePrefix X n =
  R.-_ (R._*_ X (R._*_ (aPrefix X n) (aPrefix X n)))
positiveBPrefix X n = R._*_ (R._*_ CMP102.two X) (bPrefix X n)
positiveBSquarePrefix X n =
  R._*_ (R._*_ X X) (R._*_ (bPrefix X n) (bPrefix X n))

originalGPrefix : R.ℝ → Nat → R.ℝ
originalGPrefix X n =
  R._+_
    (R._+_
      (R._+_
        (R._+_ R.1ℝ (negativeAPrefix X n))
        (negativeASquarePrefix X n))
      (positiveBPrefix X n))
    (positiveBSquarePrefix X n)

negativeAValue negativeASquareValue positiveBValue positiveBSquareValue :
  ∀ X → R._≤_ (R.∣ X ∣) Half.bishopQuarter → R.ℝ
negativeAValue X inside = R.-_ (R._*_ CMP102.two (CMP109.aSeries X inside))
negativeASquareValue X inside =
  let a = CMP109.aSeries X inside
  in R.-_ (R._*_ X (R._*_ a a))
positiveBValue X inside =
  R._*_ (R._*_ CMP102.two X) (CMP109.bSeries X inside)
positiveBSquareValue X inside =
  let b = CMP109.bSeries X inside
  in R._*_ (R._*_ X X) (R._*_ b b)

-- No new represented value: this expression is evaluated only using the
-- original aSeries/bSeries limits and CMP102's original rational two.
originalG : ∀ X → R._≤_ (R.∣ X ∣) Half.bishopQuarter → R.ℝ
originalG X inside =
  R._+_
    (R._+_
      (R._+_
        (R._+_ R.1ℝ (negativeAValue X inside))
        (negativeASquareValue X inside))
      (positiveBValue X inside))
    (positiveBSquareValue X inside)

negativeAPrefixConverges :
  ∀ X (inside : R._≤_ (R.∣ X ∣) Half.bishopQuarter) →
  Seq._ConvergesTo_ (negativeAPrefix X) (negativeAValue X inside)
negativeAPrefixConverges X inside =
  Seq.-xₙ→-x₀
    (R._*_ CMP102.two (CMP109.aSeries X inside) ,
      Seq.xₙyₙ→x₀y₀
        (CMP102.two , constantConverges CMP102.two)
        (CMP109.aSeries X inside , Same.nativeASeriesConvergesToOriginalCMP109 X inside))

negativeASquarePrefixConverges :
  ∀ X (inside : R._≤_ (R.∣ X ∣) Half.bishopQuarter) →
  Seq._ConvergesTo_ (negativeASquarePrefix X) (negativeASquareValue X inside)
negativeASquarePrefixConverges X inside =
  let a = CMP109.aSeries X inside
      aConv = Same.nativeASeriesConvergesToOriginalCMP109 X inside
  in Seq.-xₙ→-x₀
       (R._*_ X (R._*_ a a) ,
         Seq.xₙyₙ→x₀y₀
           (X , constantConverges X)
           (R._*_ a a , Seq.xₙyₙ→x₀y₀ (a , aConv) (a , aConv)))

positiveBPrefixConverges :
  ∀ X (inside : R._≤_ (R.∣ X ∣) Half.bishopQuarter) →
  Seq._ConvergesTo_ (positiveBPrefix X) (positiveBValue X inside)
positiveBPrefixConverges X inside =
  Seq.xₙyₙ→x₀y₀
    (R._*_ CMP102.two X , constantConverges (R._*_ CMP102.two X))
    (CMP109.bSeries X inside , Same.nativeBSeriesConvergesToOriginalCMP109 X inside)

positiveBSquarePrefixConverges :
  ∀ X (inside : R._≤_ (R.∣ X ∣) Half.bishopQuarter) →
  Seq._ConvergesTo_ (positiveBSquarePrefix X) (positiveBSquareValue X inside)
positiveBSquarePrefixConverges X inside =
  let b = CMP109.bSeries X inside
      bConv = Same.nativeBSeriesConvergesToOriginalCMP109 X inside
  in Seq.xₙyₙ→x₀y₀
       (R._*_ X X , constantConverges (R._*_ X X))
       (R._*_ b b , Seq.xₙyₙ→x₀y₀ (b , bConv) (b , bConv))

-- Paid source-written limit-compatibility weld for the ACTUAL G_N / G.
originalGPrefixConvergesToOriginalG :
  ∀ X (inside : R._≤_ (R.∣ X ∣) Half.bishopQuarter) →
  Seq._ConvergesTo_ (originalGPrefix X) (originalG X inside)
originalGPrefixConvergesToOriginalG X inside =
  sumConverges
    (sumConverges
      (sumConverges
        (sumConverges
          (constantConverges R.1ℝ)
          (negativeAPrefixConverges X inside))
        (negativeASquarePrefixConverges X inside))
      (positiveBPrefixConverges X inside))
    (positiveBSquarePrefixConverges X inside)

-- Only the geometric-decay-to-zero argument is outstanding. The argument
-- below is NOT an assumption that G is zero: its premise must be discharged
-- by a concrete original-prefix convergence certificate on |X|<=1/4.
originalGZeroFromOriginalPrefixConvergence :
  ∀ X (inside : R._≤_ (R.∣ X ∣) Half.bishopQuarter) →
  Seq._ConvergesTo_ (originalGPrefix X) R.0ℝ →
  R._≃_ (originalG X inside) R.0ℝ
originalGZeroFromOriginalPrefixConvergence X inside prefixToZero =
  Seq.uniqueness-of-limits
    (originalGPrefixConvergesToOriginalG X inside)
    prefixToZero
