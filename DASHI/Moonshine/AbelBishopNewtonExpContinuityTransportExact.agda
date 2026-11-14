module DASHI.Moonshine.AbelBishopNewtonExpContinuityTransportExact where

------------------------------------------------------------------------
-- NEWTON OPERATOR CONTINUITY FROM *LITERAL BISHOP EXPONENTIAL* CONTINUITY.
--
-- The Newton endomap T(z)=z-(expC(z)-z)*(expC(p0)-1)^-1 is built on the
-- original Murray/Bishop complex carrier.  Its reciprocal denominator
-- is FIXED, so native continuity of expC along the genuine Newton
-- orbit, plus the original Bishop arithmetic convergence laws,
-- supplies continuity of T along that same orbit.
--
-- There is no new "Newton continuous" input: the only analytic input
-- is convergence of the SAME literal expC applied to Newton's source
-- iteration.  The source Newton step bound is inherited unchanged.
--
-- No contraction, analytic expC continuity, or fixed-point existence
-- is asserted by itself in this module.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Product.Base using (_,_)

import Real as BishopReal
import Sequence as BishopSequence

import DASHI.Analysis.BishopComplexSeriesConvergenceExact as Complex
import DASHI.Analysis.BishopComplexAlgebraExact as Algebra
import DASHI.Analysis.BishopComplexReciprocalExact as Reciprocal
import DASHI.Analysis.BishopSetoidComplexExact as Cartesian
import DASHI.Analysis.BishopComplexConstantMultiplicationConvergenceExact as Multiply
import DASHI.Moonshine.AbelBishopOriginalComplexCarrierWeldExact as Native
import DASHI.Moonshine.AbelBishopKoenigsComponentwiseCompletionExact as Completion
import DASHI.Moonshine.AbelBishopNewtonSelectedOperatorExact as Newton
import DASHI.Moonshine.AbelBishopNewtonSelectedLimitExact as NewtonLimit

originalBishopComplexSubtractConverges :
  (left right : Nat → Complex.BishopComplex) →
  (leftLimit rightLimit : Complex.BishopComplex) →
  Completion.OriginalBishopPointwiseComplexConverges left leftLimit →
  Completion.OriginalBishopPointwiseComplexConverges right rightLimit →
  Completion.OriginalBishopPointwiseComplexConverges
    (λ n → Algebra._-C_ (left n) (right n))
    (Algebra._-C_ leftLimit rightLimit)
originalBishopComplexSubtractConverges
  left right leftLimit rightLimit leftConverges rightConverges =
  Completion.original-bishop-pointwise-complex-converges
    (Multiply.originalBishopSubtractConverges
      (λ n → Complex.re (left n))
      (λ n → Complex.re (right n))
      (Complex.re leftLimit)
      (Complex.re rightLimit)
      (Completion.realConverges leftConverges)
      (Completion.realConverges rightConverges))
    (Multiply.originalBishopSubtractConverges
      (λ n → Complex.im (left n))
      (λ n → Complex.im (right n))
      (Complex.im leftLimit)
      (Complex.im rightLimit)
      (Completion.imaginaryConverges leftConverges)
      (Completion.imaginaryConverges rightConverges))

originalBishopComplexFixedRightMultiplyConverges :
  (q : Complex.BishopComplex) →
  (trajectory : Nat → Complex.BishopComplex) →
  (limit : Complex.BishopComplex) →
  Completion.OriginalBishopPointwiseComplexConverges
    trajectory limit →
  Completion.OriginalBishopPointwiseComplexConverges
    (λ n → Algebra._*C_ (trajectory n) q)
    (Algebra._*C_ limit q)
originalBishopComplexFixedRightMultiplyConverges
  (Complex.complex c d) h (Complex.complex a b) converges =
  let
    ac =
      BishopSequence.xₙyₙ→x₀y₀
        (a , Completion.realConverges converges)
        (c , Multiply.originalBishopConstantSequenceConverges c)
    bd =
      BishopSequence.xₙyₙ→x₀y₀
        (b , Completion.imaginaryConverges converges)
        (d , Multiply.originalBishopConstantSequenceConverges d)
    ad =
      BishopSequence.xₙyₙ→x₀y₀
        (a , Completion.realConverges converges)
        (d , Multiply.originalBishopConstantSequenceConverges d)
    bc =
      BishopSequence.xₙyₙ→x₀y₀
        (b , Completion.imaginaryConverges converges)
        (c , Multiply.originalBishopConstantSequenceConverges c)
  in
  Completion.original-bishop-pointwise-complex-converges
    (Multiply.originalBishopSubtractConverges
      (λ n → BishopReal._*_ (Complex.re (h n)) c)
      (λ n → BishopReal._*_ (Complex.im (h n)) d)
      (BishopReal._*_ a c) (BishopReal._*_ b d)
      ac bd)
    (BishopSequence.xₙ+yₙ→x₀+y₀
      (BishopReal._*_ a d , ad)
      (BishopReal._*_ b c , bc))

originalBishopNewtonOperatorContinuousFromExp :
  ∀ T nz
    (bounds : NewtonLimit.OriginalBishopNewtonSelectedStepBounds T nz) →
  Completion.OriginalBishopPointwiseComplexConverges
    (λ n →
      Native.originalBishopExpOnSeries T
        (Newton.originalBishopNewtonOrbit T nz n))
    (Native.originalBishopExpOnSeries T
      (NewtonLimit.originalBishopSelectedNewtonLimit T nz bounds)) →
  Completion.OriginalBishopPointwiseComplexConverges
    (λ n →
      Newton.originalBishopNewtonOperator T nz
        (Newton.originalBishopNewtonOrbit T nz n))
    (Newton.originalBishopNewtonOperator T nz
      (NewtonLimit.originalBishopSelectedNewtonLimit T nz bounds))
originalBishopNewtonOperatorContinuousFromExp T nz bounds expConverges =
  let
    h = Newton.originalBishopNewtonOrbit T nz
    limit = NewtonLimit.originalBishopSelectedNewtonLimit T nz bounds
    hConverges =
      NewtonLimit.originalBishopSelectedNewtonConverges T nz bounds
    correction =
      λ n → Newton.originalBishopExponentialDefect T (h n)
    defectConverges =
      originalBishopComplexSubtractConverges
        (λ n → Native.originalBishopExpOnSeries T (h n))
        h
        (Native.originalBishopExpOnSeries T limit)
        limit
        expConverges
        hConverges
    q =
      Reciprocal.reciprocalC
        (Newton.originalBishopNewtonDenominator T) nz
    correctionConverges =
      originalBishopComplexFixedRightMultiplyConverges
        q correction
        (Newton.originalBishopExponentialDefect T limit)
        defectConverges
  in
  originalBishopComplexSubtractConverges
    h
    (λ n → Algebra._*C_ (correction n) q)
    limit
    (Algebra._*C_ (Newton.originalBishopExponentialDefect T limit) q)
    hConverges
    correctionConverges

originalBishopNewtonLimitExpFixedFromExpContinuity :
  ∀ T nz
    (bounds : NewtonLimit.OriginalBishopNewtonSelectedStepBounds T nz) →
  Completion.OriginalBishopPointwiseComplexConverges
    (λ n →
      Native.originalBishopExpOnSeries T
        (Newton.originalBishopNewtonOrbit T nz n))
    (Native.originalBishopExpOnSeries T
      (NewtonLimit.originalBishopSelectedNewtonLimit T nz bounds)) →
  Complex._≈C_
    (Native.originalBishopExpOnSeries T
      (NewtonLimit.originalBishopSelectedNewtonLimit T nz bounds))
    (NewtonLimit.originalBishopSelectedNewtonLimit T nz bounds)
originalBishopNewtonLimitExpFixedFromExpContinuity
  T nz bounds expConverges =
  NewtonLimit.originalBishopSelectedNewtonLimitIsNativeExpFixed
    T nz bounds
    (originalBishopNewtonOperatorContinuousFromExp
      T nz bounds expConverges)
