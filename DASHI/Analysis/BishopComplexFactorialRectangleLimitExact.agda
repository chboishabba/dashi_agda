module DASHI.Analysis.BishopComplexFactorialRectangleLimitExact where

------------------------------------------------------------------------
-- ORIGINAL FACTORIAL REAL-AXIS x IMAGINARY-AXIS RECTANGLE LIMIT.
--
-- On the literal BishopComplexSeriesConvergenceExact carrier,
-- the original finite square rectangle converges to
--
--       (exp_B(x) * cos_B(y), exp_B(x) * sin_B(y)).
--
-- This proves both source coordinates through actual finite
-- partial sums, Bishop multiplication convergence, and the
-- already-proved real-axis zero imaginary factorial terms.
--
-- No new convergence authority, Cauchy-product axiom, or complex
-- exponential definition is used. Kernel checking still pending.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Data.Rational.Unnormalised using (0ℚᵘ)

import Real as BishopReal
import RealProperties as BishopP
import Sequence as BishopSequence

import DASHI.Analysis.BishopComplexSeriesConvergenceExact as Complex
import DASHI.Analysis.BishopComplexFiniteRectangleProductExact as Rectangle
import DASHI.Analysis.BishopComplexTriangleTailsVanishingExact as Factorial
import DASHI.Analysis.BishopVanishingDifferenceConvergenceExact as Vanish
import DASHI.Foundations.BishopFiniteSeriesExtensionalityExact as Ext
import DASHI.Foundations.BishopExponentialSeriesConvergenceExact as Exp
import DASHI.Foundations.BishopPowerSeriesElementaryBridgeExact as Elementary
import DASHI.Analysis.BishopSetoidComplexExact as Cartesian
import DASHI.Moonshine.AbelBishopFactorialComplexRealAxisTermsExact as RealAxis
import DASHI.Moonshine.AbelBishopFactorialComplexImaginaryAxisFiniteReindexExact as ImagPrefix
import DASHI.Moonshine.AbelBishopFactorialImaginaryAxisAllCutoffsExact as ImagLimit

realPrefix :
  (Nat → Complex.BishopComplex) → Nat → BishopReal.ℝ
realPrefix terms n =
  BishopSequence.SeriesOf (Complex.realTerms terms) n

imagPrefix :
  (Nat → Complex.BishopComplex) → Nat → BishopReal.ℝ
imagPrefix terms n =
  BishopSequence.SeriesOf (Complex.imagTerms terms) n

originalBishopRealFactorImaginaryPrefixZero :
  ∀ x n →
  BishopReal._≃_
    (imagPrefix (Factorial.factorialRealStream x) n)
    BishopReal.0ℝ
originalBishopRealFactorImaginaryPrefixZero x n =
  BishopP.≃-trans
    (Ext.seriesPartialSumsCongruent
      (λ i → proj₂ (RealAxis.originalBishopFactorialComplexTermRealAxis x i))
      n)
    (ImagPrefix.originalBishopFiniteZeroSum n)

originalBishopRealFactorImaginaryConvergesZero :
  ∀ x →
  BishopSequence._ConvergesTo_
    (imagPrefix (Factorial.factorialRealStream x))
    BishopReal.0ℝ
originalBishopRealFactorImaginaryConvergesZero x =
  BishopSequence.xₙ≃c⇒xₙ→c
    (λ n → originalBishopRealFactorImaginaryPrefixZero x n)

-- Vanishing-difference transport handles the correction term
-- without constructing an independent negative-series calculus.
originalBishopDifferenceVanishingCorrection :
  ∀ (main correction : Nat → BishopReal.ℝ) limit →
  BishopSequence._ConvergesTo_ main limit →
  BishopSequence._ConvergesTo_ correction BishopReal.0ℝ →
  BishopSequence._ConvergesTo_
    (λ n → BishopReal._-_ (main n) (correction n))
    limit
originalBishopDifferenceVanishingCorrection
  main correction limit mainConverges correctionConverges =
  Vanish.vanishingDifferenceConvergence
    mainConverges correctionConverges
    (λ n →
      let
        a = main n
        b = correction n
        equality :
          BishopReal._≃_
            (BishopReal._-_
              (BishopReal._-_ a b) a)
            (BishopReal.-_ b)
        equality =
          let open BishopP.ℝ-Solver in
          solve 2
            (λ a′ b′ → (a′ ⊖ b′) ⊖ a′ ⊜ ⊝ b′)
            BishopP.≃-refl a b
      in
      BishopP.≤-reflexive
        (BishopP.≃-trans
          (BishopP.∣-∣-cong equality)
          BishopP.∣-x∣≃∣x∣))

originalBishopAdditionVanishingCorrection :
  ∀ (main correction : Nat → BishopReal.ℝ) limit →
  BishopSequence._ConvergesTo_ main limit →
  BishopSequence._ConvergesTo_ correction BishopReal.0ℝ →
  BishopSequence._ConvergesTo_
    (λ n → BishopReal._+_ (main n) (correction n))
    limit
originalBishopAdditionVanishingCorrection
  main correction limit mainConverges correctionConverges =
  Vanish.vanishingDifferenceConvergence
    mainConverges correctionConverges
    (λ n →
      let
        a = main n
        b = correction n
        equality :
          BishopReal._≃_
            (BishopReal._-_
              (BishopReal._+_ a b) a)
            b
        equality =
          let open BishopP.ℝ-Solver in
          solve 2
            (λ a′ b′ → (a′ ⊕ b′) ⊖ a′ ⊜ b′)
            BishopP.≃-refl a b
      in
      BishopP.≤-reflexive
        (BishopP.∣-∣-cong equality))

originalBishopRealImaginaryProductZero :
  ∀ (right : Nat → BishopReal.ℝ) (rightLimit : BishopReal.ℝ) x →
  BishopSequence._ConvergesTo_ right rightLimit →
  BishopSequence._ConvergesTo_
    (λ n → BishopReal._*_
      (imagPrefix (Factorial.factorialRealStream x) n)
      (right n))
    BishopReal.0ℝ
originalBishopRealImaginaryProductZero right rightLimit x rightConverges =
  BishopSequence.xₙ→x∧x≃y⇒xₙ→y
    (BishopSequence.xₙyₙ→x₀y₀
      (BishopReal.0ℝ ,
        originalBishopRealFactorImaginaryConvergesZero x)
      (rightLimit , rightConverges))
    (let open BishopP.ℝ-Solver in
     solve 1 (λ r → Κ 0ℚᵘ ⊗ r ⊜ Κ 0ℚᵘ)
       BishopP.≃-refl rightLimit)

-- Source finite square rectangle: the first original factor is
-- the actual factorial series on (x,0), and the second on (0,y).
originalBishopFactorialRectangleRealConverges :
  (T : Cartesian.BishopSetoidComplexTranscendentals) →
  ∀ x y →
  BishopSequence._ConvergesTo_
    (λ n → Complex.re
      (Rectangle.rectangleComplex
        (Factorial.factorialRealStream x)
        (Factorial.factorialImaginaryStream y) n n))
    (BishopReal._*_
      (Exp.bishopExp x)
      (Elementary.bishopCos (Cartesian.dataSet T) y))
originalBishopFactorialRectangleRealConverges T x y =
  let
    left = Factorial.factorialRealStream x
    right = Factorial.factorialImaginaryStream y
    cos = Elementary.bishopCos (Cartesian.dataSet T) y
    sin = Elementary.bishopSin (Cartesian.dataSet T) y
    a n = realPrefix left n
    b n = imagPrefix left n
    c n = realPrefix right n
    d n = imagPrefix right n
    mainConvergence =
      BishopSequence.xₙyₙ→x₀y₀
        (Exp.bishopExp x ,
          RealAxis.originalBishopRealAxisFactorialSeriesConvergesToOriginalExp x)
        (cos , ImagLimit.originalBishopImaginaryFactorialRealAllCutoffs T y)
    productConvergence =
      originalBishopDifferenceVanishingCorrection
        (λ n → BishopReal._*_ (a n) (c n))
        (λ n → BishopReal._*_ (b n) (d n))
        (BishopReal._*_ (Exp.bishopExp x) cos)
        mainConvergence
        (originalBishopRealImaginaryProductZero
          d sin x
          (ImagLimit.originalBishopImaginaryFactorialImagAllCutoffs T y))
  in
  BishopSequence.xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀
    (λ n →
      BishopP.≃-symm
        (proj₁ (Rectangle.originalBishopComplexSquareRectangleProduct
          left right n)))
    ((BishopReal._*_ (Exp.bishopExp x) cos) , productConvergence)

originalBishopFactorialRectangleImagConverges :
  (T : Cartesian.BishopSetoidComplexTranscendentals) →
  ∀ x y →
  BishopSequence._ConvergesTo_
    (λ n → Complex.im
      (Rectangle.rectangleComplex
        (Factorial.factorialRealStream x)
        (Factorial.factorialImaginaryStream y) n n))
    (BishopReal._*_
      (Exp.bishopExp x)
      (Elementary.bishopSin (Cartesian.dataSet T) y))
originalBishopFactorialRectangleImagConverges T x y =
  let
    left = Factorial.factorialRealStream x
    right = Factorial.factorialImaginaryStream y
    cos = Elementary.bishopCos (Cartesian.dataSet T) y
    sin = Elementary.bishopSin (Cartesian.dataSet T) y
    a n = realPrefix left n
    b n = imagPrefix left n
    c n = realPrefix right n
    d n = imagPrefix right n
    mainConvergence =
      BishopSequence.xₙyₙ→x₀y₀
        (Exp.bishopExp x ,
          RealAxis.originalBishopRealAxisFactorialSeriesConvergesToOriginalExp x)
        (sin , ImagLimit.originalBishopImaginaryFactorialImagAllCutoffs T y)
    productConvergence =
      originalBishopAdditionVanishingCorrection
        (λ n → BishopReal._*_ (a n) (d n))
        (λ n → BishopReal._*_ (b n) (c n))
        (BishopReal._*_ (Exp.bishopExp x) sin)
        mainConvergence
        (originalBishopRealImaginaryProductZero
          c cos x
          (ImagLimit.originalBishopImaginaryFactorialRealAllCutoffs T y))
  in
  BishopSequence.xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀
    (λ n →
      BishopP.≃-symm
        (proj₂ (Rectangle.originalBishopComplexSquareRectangleProduct
          left right n)))
    ((BishopReal._*_ (Exp.bishopExp x) sin) , productConvergence)
