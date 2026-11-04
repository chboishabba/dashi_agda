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

open import Agda.Builtin.Nat using (Nat)
open import Data.Product.Base using (_×_; _,_)

import Real as R
import RealProperties as RP
import Sequence as Seq

import DASHI.Analysis.BishopSetoidComplexExact as C
import DASHI.Foundations.BishopFiniteSeriesRectangleProductExact as Rect
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
    (C.re (C.imaginaryPhase T x) ,
      Route.round11MachinCosineConverges inputs x)
    (RP.≃-symm (C.reEquivalent phaseEquality))
  ,
  Seq.xₙ→x∧x≃y⇒xₙ→y
    (C.im (C.imaginaryPhase T x) ,
      Route.round11MachinSineConverges inputs x)
    (RP.≃-symm (C.imEquivalent phaseEquality))
