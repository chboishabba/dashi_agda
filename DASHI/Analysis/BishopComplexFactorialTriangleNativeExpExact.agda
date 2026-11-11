module DASHI.Analysis.BishopComplexFactorialTriangleNativeExpExact where

------------------------------------------------------------------------
-- ORIGINAL BISHOP FACTORIAL CAUCHY TRIANGLE -> NATIVE expC.
--
-- This is the actual source-valued analytic limit on all x,y:
--   lim_N sum_(k<N) sum_(i+j=k) x^i/i! (iy)^j/j!
--         = exp_B(x) (cos_B(y) + i sin_B(y))
--         = original BishopSetoidComplexExact.expC(x+iy).
--
-- Uses the actual Bishop four-wing vanishing certificate plus
-- the rectangular limit. No new complex exponential authority.
--
-- Still separate: prove the ORIGINAL finite complex binomial
-- identity identifying triangle coefficients with (x+iy)^n/n!.
-- No claim of full factorial expC equality yet.
------------------------------------------------------------------------

open import Data.Product.Base using (_×_; _,_)
import Real as BishopReal
import Sequence as BishopSequence

import DASHI.Analysis.BishopComplexSeriesConvergenceExact as Complex
import DASHI.Analysis.BishopSetoidComplexExact as Cartesian
import DASHI.Analysis.BishopComplexFiniteSquareTriangleDifferenceExact as Wing
import DASHI.Analysis.BishopComplexTriangleTailsVanishingExact as Factorial
import DASHI.Analysis.BishopComplexCauchyTriangleLimitTransportExact as Transport
import DASHI.Analysis.BishopComplexFactorialRectangleLimitExact as RectangleLimit
import DASHI.Moonshine.AbelBishopOriginalComplexCarrierWeldExact as Weld

originalBishopFactorialTriangleConvergesToNativeExp :
  (T : Cartesian.BishopSetoidComplexTranscendentals) →
  ∀ x y →
  BishopSequence._ConvergesTo_
    (λ n → Complex.re
      (Wing.cauchyTrianglePartial
        (Factorial.factorialRealStream x)
        (Factorial.factorialImaginaryStream y) n))
    (Complex.re
      (Weld.originalBishopExpOnSeries T (Complex.complex x y)))
  ×
  BishopSequence._ConvergesTo_
    (λ n → Complex.im
      (Wing.cauchyTrianglePartial
        (Factorial.factorialRealStream x)
        (Factorial.factorialImaginaryStream y) n))
    (Complex.im
      (Weld.originalBishopExpOnSeries T (Complex.complex x y)))
originalBishopFactorialTriangleConvergesToNativeExp T x y =
  Transport.originalBishopFactorialTriangleFromRectangle
    x y
    (Weld.originalBishopExpOnSeries T (Complex.complex x y))
    (RectangleLimit.originalBishopFactorialRectangleRealConverges T x y)
    (RectangleLimit.originalBishopFactorialRectangleImagConverges T x y)
