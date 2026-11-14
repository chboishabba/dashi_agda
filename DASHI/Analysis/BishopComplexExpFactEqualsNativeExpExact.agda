module DASHI.Analysis.BishopComplexExpFactEqualsNativeExpExact where

------------------------------------------------------------------------
-- P1 CAPSTONE: ORIGINAL COMPLEX FACTORIAL SERIES = NATIVE expC.
--
-- For arbitrary Bishop-real x,y and the repository's configured
-- BishopSetoidComplexTranscendentals T, the *literal* all-degree
-- factorial series of the exact Cartesian input (x,y) converges
-- in both original Bishop coordinates to native expC T (x+iy).
--
-- This combines, without any assumed complex product theorem:
--  (1) original real/imaginary factorial convergence on every cutoff;
--  (2) finite original Bishop-complex rectangle product;
--  (3) original four-wing absolute majorants and vanishing moduli;
--  (4) original rectangle -> Cauchy triangle limit transport;
--  (5) stdlib complex semiring/binomial power theorem on SAME carrier;
--  (6) original reciprocal-factorial binomial finite coefficient;
--  (7) exact finite coefficient-to-Cauchy triangle weld;
--  (8) original source-valued finite-to-infinite convergence transport.
--
-- This is SOURCE-WRITTEN, NOT AGDA KERNEL VERIFIED.
-- No uninhabited closing leaf or postulate is imported.
------------------------------------------------------------------------

open import Data.Product.Base using (_×_; proj₁; proj₂)
import Real as BishopReal
import Sequence as BishopSequence

import DASHI.Analysis.BishopComplexSeriesConvergenceExact as Complex
import DASHI.Analysis.BishopSetoidComplexExact as Cartesian
import DASHI.Analysis.BishopComplexExpFactFiniteBinomialReductionExact as Reduction
import DASHI.Analysis.BishopComplexFactorialBinomialCapstoneExact as Binomial
import DASHI.Moonshine.AbelBishopFactorialComplexRealAxisTermsExact as Factorial
import DASHI.Moonshine.AbelBishopOriginalComplexCarrierWeldExact as Weld

originalBishopExpFactEqualsNativeExp :
  (T : Cartesian.BishopSetoidComplexTranscendentals) →
  ∀ (x y : BishopReal.ℝ) →
  BishopSequence._ConvergesTo_
    (BishopSequence.SeriesOf
      (Complex.realTerms
        (Factorial.originalBishopFactorialComplexTerm
          (Complex.complex x y))))
    (Complex.re
      (Weld.originalBishopExpOnSeries T (Complex.complex x y)))
  ×
  BishopSequence._ConvergesTo_
    (BishopSequence.SeriesOf
      (Complex.imagTerms
        (Factorial.originalBishopFactorialComplexTerm
          (Complex.complex x y))))
    (Complex.im
      (Weld.originalBishopExpOnSeries T (Complex.complex x y)))
originalBishopExpFactEqualsNativeExp T x y =
  Reduction.originalBishopFactorialSeriesEqualsNativeExpFromFiniteBinomial
    T x y
    (Binomial.originalBishopFiniteComplexBinomialLeafInhabited x y)


-- Canonical complex-series consumer on exactly the same original
-- factor terms, not just a pair of scalar convergence facts.
originalBishopExpFactComplexSeriesConvergesToNativeExp :
  (T : Cartesian.BishopSetoidComplexTranscendentals) →
  ∀ (x y : BishopReal.ℝ) →
  Complex.ComplexSeriesConvergesTo
    (Factorial.originalBishopFactorialComplexTerm
      (Complex.complex x y))
    (Weld.originalBishopExpOnSeries T (Complex.complex x y))
originalBishopExpFactComplexSeriesConvergesToNativeExp T x y =
  let components = originalBishopExpFactEqualsNativeExp T x y
  in
  Complex.complex-series-converges-to
    (proj₁ components)
    (proj₂ components)
