module DASHI.Analysis.BishopComplexConstantMultiplicationConvergenceExact where

------------------------------------------------------------------------
-- ACTUAL BISHOP-SETIOD COMPLEX SCALAR MULTIPLICATION CONTINUITY.
--
-- On the literal original BishopComplex pair, show that
--
--      h_n -> h   implies   p *C h_n -> p *C h
--
-- by two real products, additive convergence and negation.
-- All convergence moduli are directly inherited from the pinned
-- vendored Bishop Sequence API, not postulated.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Product.Base using (_,_)

import Real as BishopReal
import RealProperties as BishopP
import Sequence as BishopSequence

import DASHI.Analysis.BishopComplexSeriesConvergenceExact as Complex
import DASHI.Analysis.BishopComplexAlgebraExact as Algebra
import DASHI.Moonshine.AbelBishopKoenigsComponentwiseCompletionExact as Completion

originalBishopConstantSequenceConverges :
  (value : BishopReal.ℝ) →
  BishopSequence._ConvergesTo_ (λ (_ : Nat) → value) value
originalBishopConstantSequenceConverges value =
  BishopSequence.xₙ≃c⇒xₙ→c
    (λ {(suc n-1) → BishopP.≃-refl})

originalBishopMultiplyConstantConverges :
  (scalar : BishopReal.ℝ) →
  (sequence : Nat → BishopReal.ℝ) →
  (limit : BishopReal.ℝ) →
  BishopSequence._ConvergesTo_ sequence limit →
  BishopSequence._ConvergesTo_
    (λ n → BishopReal._*_ scalar (sequence n))
    (BishopReal._*_ scalar limit)
originalBishopMultiplyConstantConverges scalar sequence limit converges =
  BishopSequence.xₙyₙ→x₀y₀
    (scalar , originalBishopConstantSequenceConverges scalar)
    (limit , converges)

originalBishopSubtractConverges :
  (left right : Nat → BishopReal.ℝ) →
  (leftLimit rightLimit : BishopReal.ℝ) →
  BishopSequence._ConvergesTo_ left leftLimit →
  BishopSequence._ConvergesTo_ right rightLimit →
  BishopSequence._ConvergesTo_
    (λ n → BishopReal._-_ (left n) (right n))
    (BishopReal._-_ leftLimit rightLimit)
originalBishopSubtractConverges
  left right leftLimit rightLimit leftConverges rightConverges =
  BishopSequence.xₙ+yₙ→x₀+y₀
    (leftLimit , leftConverges)
    (BishopReal.- rightLimit ,
      BishopSequence.-xₙ→-x₀ (rightLimit , rightConverges))

originalBishopConstantComplexMultiplyConverges :
  (p : Complex.BishopComplex) →
  (h : Nat → Complex.BishopComplex) →
  (limit : Complex.BishopComplex) →
  Completion.OriginalBishopPointwiseComplexConverges h limit →
  Completion.OriginalBishopPointwiseComplexConverges
    (λ n → Algebra._*C_ p (h n))
    (Algebra._*C_ p limit)
originalBishopConstantComplexMultiplyConverges
  (Complex.complex a b) h (Complex.complex c d) converges =
  let
    realPart = λ n → Complex.re (h n)
    imaginaryPart = λ n → Complex.im (h n)
    acConverges =
      originalBishopMultiplyConstantConverges
        a realPart c (Completion.realConverges converges)
    bdConverges =
      originalBishopMultiplyConstantConverges
        b imaginaryPart d (Completion.imaginaryConverges converges)
    adConverges =
      originalBishopMultiplyConstantConverges
        a imaginaryPart d (Completion.imaginaryConverges converges)
    bcConverges =
      originalBishopMultiplyConstantConverges
        b realPart c (Completion.realConverges converges)
  in
  Completion.original-bishop-pointwise-complex-converges
    (originalBishopSubtractConverges
      (λ n → BishopReal._*_ a (realPart n))
      (λ n → BishopReal._*_ b (imaginaryPart n))
      (BishopReal._*_ a c)
      (BishopReal._*_ b d)
      acConverges bdConverges)
    (BishopSequence.xₙ+yₙ→x₀+y₀
      (BishopReal._*_ a d , adConverges)
      (BishopReal._*_ b c , bcConverges))
