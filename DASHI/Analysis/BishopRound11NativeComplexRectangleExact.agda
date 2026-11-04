{-# OPTIONS --safe #-}
module DASHI.Analysis.BishopRound11NativeComplexRectangleExact where

------------------------------------------------------------------------
-- K05-PRODUCT: THE FINITE CARTESIAN RECTANGLE ON THE ACTUAL
-- BISHOP SETOID COMPLEX CARRIER, NOT A SECOND COMPLEX SEMIRING.
--
-- The real finite rectangle theorem is reused FOUR times.  The
-- resulting complex identity is unconditional for every pair of
-- Bishop-complex term histories, and is then instantiated with the
-- original Round11 signed-factorial sine and cosine terms.
--
-- The literal phase series also converges coordinatewise to the
-- actual expC(i*x), by the original Round11 convergence theorems.
--
-- STILL REQUIRED for K05-PRODUCT: coefficientwise identification
-- of the triangular mixed signed-factorial convolution with the
-- terms at x+y, and the complex rectangle/triangle wing limit.
-- Neither is assumed or claimed by this file.
--
-- Attribution: Cauchy; Bishop and Bridges (1985); Murray (2022);
-- Csimma's pinned Bishop implementation; existing DASHI real
-- rectangle, Round11 signed-factorial and complex-series authors.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)

import Real as R
import RealProperties as RP
import Sequence as Seq

import DASHI.Analysis.BishopSetoidComplexExact as C
import DASHI.Foundations.BishopFiniteSeriesRectangleProductExact as Rect
import DASHI.Foundations.BishopFiniteCauchyRowReindexExact as Row
import DASHI.Moonshine.BishopRound11MachinSetoidComplexInstanceExact as Route
import DASHI.Physics.YangMills.BalabanBishopConcreteSineCosineTermParityExact as Concrete
import DASHI.Physics.YangMills.YangMillsSubmissionRound11ExactCutset as Round11

realTerms : (Nat → C.BishopComplex) → Nat → R.ℝ
realTerms terms n = C.re (terms n)

imagTerms : (Nat → C.BishopComplex) → Nat → R.ℝ
imagTerms terms n = C.im (terms n)

complexFinitePartial :
  (Nat → C.BishopComplex) → Nat → C.BishopComplex
complexFinitePartial terms count =
  C.complex
    (Seq.SeriesOf (realTerms terms) count)
    (Seq.SeriesOf (imagTerms terms) count)

-- Four literal real rectangles assemble into a SINGLE rectangle on
-- the selected Bishop setoid-complex Cartesian multiplication.
complexRectangle :
  (left right : Nat → C.BishopComplex) →
  Nat → Nat → C.BishopComplex
complexRectangle left right height width =
  C.complex
    (R._-_
      (Rect.rectangleSum (realTerms left) (realTerms right)
        height width)
      (Rect.rectangleSum (imagTerms left) (imagTerms right)
        height width))
    (R._+_
      (Rect.rectangleSum (realTerms left) (imagTerms right)
        height width)
      (Rect.rectangleSum (imagTerms left) (realTerms right)
        height width))

-- Genuine finite complex product, without a synthetic complex
-- semiring or a new summation oracle.  The two coordinates are
-- exactly the existing real rectangleProduct theorem.
complexFiniteRectangleProduct :
  (left right : Nat → C.BishopComplex) →
  (height width : Nat) →
  C._≈C_
    (complexRectangle left right height width)
    (C._*C_
      (complexFinitePartial left height)
      (complexFinitePartial right width))
complexFiniteRectangleProduct left right height width =
  C.complex-equivalent
    (RP.+-cong
      (Rect.rectangleProduct (realTerms left) (realTerms right)
        height width)
      (RP.-‿cong
        (Rect.rectangleProduct (imagTerms left) (imagTerms right)
          height width)))
    (RP.+-cong
      (Rect.rectangleProduct (realTerms left) (imagTerms right)
        height width)
      (Rect.rectangleProduct (imagTerms left) (realTerms right)
        height width))

-- The actual original signed-factorial terms; do not replace them
-- with a newly declared complex exponential coefficient family.
round11PhaseTerms :
  (inputs : Round11.Round11BishopCutset) →
  R.ℝ → Nat → C.BishopComplex
round11PhaseTerms inputs x n =
  C.complex
    (Concrete.cosineSignedTerm x n)
    (Concrete.sineSignedTerm x n)

round11PhaseRectangleIsProduct :
  (inputs : Round11.Round11BishopCutset) →
  (x y : R.ℝ) →
  (height width : Nat) →
  C._≈C_
    (complexRectangle
      (round11PhaseTerms inputs x)
      (round11PhaseTerms inputs y)
      height width)
    (C._*C_
      (complexFinitePartial (round11PhaseTerms inputs x) height)
      (complexFinitePartial (round11PhaseTerms inputs y) width))
round11PhaseRectangleIsProduct inputs x y height width =
  complexFiniteRectangleProduct
    (round11PhaseTerms inputs x)
    (round11PhaseTerms inputs y)
    height width

-- The original TWO real convergence witnesses now form a single
-- same-object complex-series convergence statement at actual expC.
round11PhaseSeriesConvergesToOriginalExp :
  (inputs : Round11.Round11BishopCutset) →
  (x : R.ℝ) →
  (Seq._ConvergesTo_
    (λ count →
      C.re (complexFinitePartial (round11PhaseTerms inputs x) count))
    (C.re
      (C.expC (Route.round11MachinTranscendentals inputs)
        (C.pureImaginary x))))
  ×
  (Seq._ConvergesTo_
    (λ count →
      C.im (complexFinitePartial (round11PhaseTerms inputs x) count))
    (C.im
      (C.expC (Route.round11MachinTranscendentals inputs)
        (C.pureImaginary x))))
round11PhaseSeriesConvergesToOriginalExp inputs x =
  let
    T = Route.round11MachinTranscendentals inputs
    phaseEquality = C.imaginaryExponentialIsPhase T x
  in
  Seq.xₙ→x∧x≃y⇒xₙ→y
    (Route.round11MachinCosineConverges inputs x)
    (RP.≃-symm (C.reEquivalent phaseEquality))
  ,
  Seq.xₙ→x∧x≃y⇒xₙ→y
    (Route.round11MachinSineConverges inputs x)
    (RP.≃-symm (C.imEquivalent phaseEquality))

------------------------------------------------------------------------
-- INFINITE RECTANGLE (NOT YET THE INFINITE CAUCHY TRIANGLE).
--
-- Constructive finite products already converge to the product of
-- their Bishop limits by the pinned Sequence multiplication theorem.
-- The four coordinate products and the two coordinate sums suffice.
-- The finite rectangle identity transports convergence to the
-- actual complex rectangular partial sums.  No new analytic input.
------------------------------------------------------------------------

ComplexFinitePartialConvergesTo :
  (terms : Nat → C.BishopComplex) →
  C.BishopComplex → Set
ComplexFinitePartialConvergesTo terms limit =
  (Seq._ConvergesTo_
    (λ n → C.re (complexFinitePartial terms n))
    (C.re limit))
  ×
  (Seq._ConvergesTo_
    (λ n → C.im (complexFinitePartial terms n))
    (C.im limit))

complexFinitePartialProductsConverge :
  (left right : Nat → C.BishopComplex) →
  (leftLimit rightLimit : C.BishopComplex) →
  ComplexFinitePartialConvergesTo left leftLimit →
  ComplexFinitePartialConvergesTo right rightLimit →
  (Seq._ConvergesTo_
    (λ n →
      C.re (C._*C_
        (complexFinitePartial left n)
        (complexFinitePartial right n)))
    (C.re (C._*C_ leftLimit rightLimit)))
  ×
  (Seq._ConvergesTo_
    (λ n →
      C.im (C._*C_
        (complexFinitePartial left n)
        (complexFinitePartial right n)))
    (C.im (C._*C_ leftLimit rightLimit)))
complexFinitePartialProductsConverge
    left right leftLimit rightLimit leftConv rightConv =
  let
    realReal =
      Seq.xₙyₙ→x₀y₀
        (C.re leftLimit , proj₁ leftConv)
        (C.re rightLimit , proj₁ rightConv)
    imagImag =
      Seq.xₙyₙ→x₀y₀
        (C.im leftLimit , proj₂ leftConv)
        (C.im rightLimit , proj₂ rightConv)
    realImag =
      Seq.xₙyₙ→x₀y₀
        (C.re leftLimit , proj₁ leftConv)
        (C.im rightLimit , proj₂ rightConv)
    imagReal =
      Seq.xₙyₙ→x₀y₀
        (C.im leftLimit , proj₂ leftConv)
        (C.re rightLimit , proj₁ rightConv)
  in
  Seq.xₙ+yₙ→x₀+y₀
    (R._*_ (C.re leftLimit) (C.re rightLimit) , realReal)
    (R.-_ (R._*_ (C.im leftLimit) (C.im rightLimit)) ,
      Seq.-xₙ→-x₀
        (R._*_ (C.im leftLimit) (C.im rightLimit) , imagImag))
  ,
  Seq.xₙ+yₙ→x₀+y₀
    (R._*_ (C.re leftLimit) (C.im rightLimit) , realImag)
    (R._*_ (C.im leftLimit) (C.re rightLimit) , imagReal)

complexRectangleConvergesToProduct :
  (left right : Nat → C.BishopComplex) →
  (leftLimit rightLimit : C.BishopComplex) →
  ComplexFinitePartialConvergesTo left leftLimit →
  ComplexFinitePartialConvergesTo right rightLimit →
  (Seq._ConvergesTo_
    (λ n → C.re (complexRectangle left right n n))
    (C.re (C._*C_ leftLimit rightLimit)))
  ×
  (Seq._ConvergesTo_
    (λ n → C.im (complexRectangle left right n n))
    (C.im (C._*C_ leftLimit rightLimit)))
complexRectangleConvergesToProduct
    left right leftLimit rightLimit leftConv rightConv =
  let
    productConv =
      complexFinitePartialProductsConverge
        left right leftLimit rightLimit leftConv rightConv
  in
  Seq.xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀
    (λ {(suc n) →
      RP.≃-symm
        (C.reEquivalent
          (complexFiniteRectangleProduct left right
            (suc n) (suc n)))})
    (C.re (C._*C_ leftLimit rightLimit) , proj₁ productConv)
  ,
  Seq.xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀
    (λ {(suc n) →
      RP.≃-symm
        (C.imEquivalent
          (complexFiniteRectangleProduct left right
            (suc n) (suc n)))})
    (C.im (C._*C_ leftLimit rightLimit) , proj₂ productConv)

-- This is now the literal original Bishop/Round11 series PRODUCT
-- LIMIT (rectangular order).  The remaining K05 proof has to show
-- that the signed-factorial TRIANGLE at x+y has that same limit.
round11RectangleConvergesToOriginalExpProduct :
  (inputs : Round11.Round11BishopCutset) →
  (x y : R.ℝ) →
  (Seq._ConvergesTo_
    (λ n →
      C.re
        (complexRectangle
          (round11PhaseTerms inputs x)
          (round11PhaseTerms inputs y) n n))
    (C.re
      (C._*C_
        (C.expC (Route.round11MachinTranscendentals inputs)
          (C.pureImaginary x))
        (C.expC (Route.round11MachinTranscendentals inputs)
          (C.pureImaginary y)))))
  ×
  (Seq._ConvergesTo_
    (λ n →
      C.im
        (complexRectangle
          (round11PhaseTerms inputs x)
          (round11PhaseTerms inputs y) n n))
    (C.im
      (C._*C_
        (C.expC (Route.round11MachinTranscendentals inputs)
          (C.pureImaginary x))
        (C.expC (Route.round11MachinTranscendentals inputs)
          (C.pureImaginary y)))))
round11RectangleConvergesToOriginalExpProduct inputs x y =
  complexRectangleConvergesToProduct
    (round11PhaseTerms inputs x)
    (round11PhaseTerms inputs y)
    (C.expC (Route.round11MachinTranscendentals inputs)
      (C.pureImaginary x))
    (C.expC (Route.round11MachinTranscendentals inputs)
      (C.pureImaginary y))
    (round11PhaseSeriesConvergesToOriginalExp inputs x)
    (round11PhaseSeriesConvergesToOriginalExp inputs y)


------------------------------------------------------------------------
-- FINITE COMPLEX TRIANGLE: REUSE THE ORIGINAL REAL MER TENS ROW
-- IDENTITY FOUR TIMES.  This remains on the *same* Bishop-complex
-- carrier and preserves the original grouped Round11 term histories.
------------------------------------------------------------------------

complexTriangle :
  (left right : Nat → C.BishopComplex) →
  Nat → C.BishopComplex
complexTriangle left right count =
  C.complex
    (R._-_
      (Row.trianglePartial (realTerms left) (realTerms right) count)
      (Row.trianglePartial (imagTerms left) (imagTerms right) count))
    (R._+_
      (Row.trianglePartial (realTerms left) (imagTerms right) count)
      (Row.trianglePartial (imagTerms left) (realTerms right) count))

complexMertensRow :
  (left right : Nat → C.BishopComplex) →
  Nat → C.BishopComplex
complexMertensRow left right count =
  C.complex
    (R._-_
      (Row.mertensRowPartial (realTerms left) (realTerms right) count)
      (Row.mertensRowPartial (imagTerms left) (imagTerms right) count))
    (R._+_
      (Row.mertensRowPartial (realTerms left) (imagTerms right) count)
      (Row.mertensRowPartial (imagTerms left) (realTerms right) count))

complexTriangleIsMertens :
  (left right : Nat → C.BishopComplex) →
  (count : Nat) →
  C._≈C_
    (complexTriangle left right count)
    (complexMertensRow left right count)
complexTriangleIsMertens left right count =
  C.complex-equivalent
    (RP.+-cong
      (Row.triangleIsMertensRow
        (realTerms left) (realTerms right) count)
      (RP.-‿cong
        (Row.triangleIsMertensRow
          (imagTerms left) (imagTerms right) count)))
    (RP.+-cong
      (Row.triangleIsMertensRow
        (realTerms left) (imagTerms right) count)
      (Row.triangleIsMertensRow
        (imagTerms left) (realTerms right) count))

round11PhaseTriangleIsMertens :
  (inputs : Round11.Round11BishopCutset) →
  (x y : R.ℝ) →
  (count : Nat) →
  C._≈C_
    (complexTriangle
      (round11PhaseTerms inputs x)
      (round11PhaseTerms inputs y) count)
    (complexMertensRow
      (round11PhaseTerms inputs x)
      (round11PhaseTerms inputs y) count)
round11PhaseTriangleIsMertens inputs x y count =
  complexTriangleIsMertens
    (round11PhaseTerms inputs x)
    (round11PhaseTerms inputs y) count
