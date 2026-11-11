module DASHI.Analysis.BishopComplexFiniteRectangleProductExact where

------------------------------------------------------------------------
-- ORIGINAL BISHOP-COMPLEX FINITE RECTANGLE PRODUCT.
--
-- Generic for arbitrary literal Bishop complex term streams a,b:
--
--  R_(h,w)(a,b) ~= (sum_(i<h) a_i) *C (sum_(j<w) b_j)
--
-- This module does not posit a complex Cauchy-product theorem.
-- It is a componentwise lift of the existing Bishop REAL rectangle
-- owner, with the complex arithmetic on the SAME source carrier.
-- Finite rectangular algebra only; triangular wing and convergence
-- are separate analytic obligations.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Product.Base using (_,_)
import Real as BishopReal
import RealProperties as BishopP
import Sequence as BishopSequence

import DASHI.Analysis.BishopComplexSeriesConvergenceExact as Complex
import DASHI.Analysis.BishopComplexAlgebraExact as Algebra
import DASHI.Foundations.BishopFiniteSeriesRectangleProductExact as Rectangle

finiteComplexPartial :
  (Nat → Complex.BishopComplex) → Nat → Complex.BishopComplex
finiteComplexPartial terms n =
  Complex.complex
    (BishopSequence.SeriesOf (Complex.realTerms terms) n)
    (BishopSequence.SeriesOf (Complex.imagTerms terms) n)

rectangleComplex :
  (left right : Nat → Complex.BishopComplex) →
  Nat → Nat → Complex.BishopComplex
rectangleComplex left right h w =
  let
    a = Complex.realTerms left
    b = Complex.imagTerms left
    c = Complex.realTerms right
    d = Complex.imagTerms right
  in
  Complex.complex
    (BishopReal._-_
      (Rectangle.rectangleSum a c h w)
      (Rectangle.rectangleSum b d h w))
    (BishopReal._+_
      (Rectangle.rectangleSum a d h w)
      (Rectangle.rectangleSum b c h w))

originalBishopComplexFiniteRectangleProduct :
  (left right : Nat → Complex.BishopComplex) →
  ∀ h w →
  Complex._≈C_
    (rectangleComplex left right h w)
    (Algebra._*C_
      (finiteComplexPartial left h)
      (finiteComplexPartial right w))
originalBishopComplexFiniteRectangleProduct left right h w =
  let
    a = Complex.realTerms left
    b = Complex.imagTerms left
    c = Complex.realTerms right
    d = Complex.imagTerms right
    realPart =
      BishopP.+-cong
        (Rectangle.rectangleProduct a c h w)
        (BishopP.-‿cong
          (Rectangle.rectangleProduct b d h w))
    imaginaryPart =
      BishopP.+-cong
        (Rectangle.rectangleProduct a d h w)
        (Rectangle.rectangleProduct b c h w)
  in
  realPart , imaginaryPart

originalBishopComplexSquareRectangleProduct :
  (left right : Nat → Complex.BishopComplex) →
  ∀ count →
  Complex._≈C_
    (rectangleComplex left right count count)
    (Algebra._*C_
      (finiteComplexPartial left count)
      (finiteComplexPartial right count))
originalBishopComplexSquareRectangleProduct left right count =
  originalBishopComplexFiniteRectangleProduct left right count count
