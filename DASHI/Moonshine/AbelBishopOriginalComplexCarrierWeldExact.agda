module DASHI.Moonshine.AbelBishopOriginalComplexCarrierWeldExact where

------------------------------------------------------------------------
-- SAME VENDORED BISHOP REAL CARRIER / TWO COMPLEX RECORD PRESENTATIONS
--
-- DASHI.Analysis.BishopSetoidComplexExact owns the literal Bishop
-- complex exponential. BishopComplexSeriesConvergenceExact owns the
-- componentwise Bishop Cauchy/series limit. The records are not
-- definitionally equal; their re/im fields share the original Real.ℝ.
--
-- No postulate; preserve the original setoid equality explicitly.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Product using (_,_)

import Real as BishopReal
import RealProperties as BishopP
import DASHI.Analysis.BishopSetoidComplexExact as Exp
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as Series
import DASHI.Analysis.BishopComplexAlgebraExact as Algebra

toSeries : Exp.BishopComplex → Series.BishopComplex
toSeries (Exp.complex a b) = Series.complex a b

toExponential : Series.BishopComplex → Exp.BishopComplex
toExponential (Series.complex a b) = Exp.complex a b

toExpAfterSeries :
  (z : Series.BishopComplex) →
  toSeries (toExponential z) ≡ z
toExpAfterSeries (Series.complex a b) = refl

toSeriesAfterExp :
  (z : Exp.BishopComplex) →
  toExponential (toSeries z) ≡ z
toSeriesAfterExp (Exp.complex a b) = refl

originalExpEquivalenceToSeries :
  ∀ {x y : Exp.BishopComplex} →
  Exp._≈C_ x y →
  Series._≈C_ (toSeries x) (toSeries y)
originalExpEquivalenceToSeries equivalent =
  Exp.reEquivalent equivalent , Exp.imEquivalent equivalent

originalSeriesEquivalenceToExp :
  ∀ {x y : Series.BishopComplex} →
  Series._≈C_ x y →
  Exp._≈C_ (toExponential x) (toExponential y)
originalSeriesEquivalenceToExp (re≈ , im≈) =
  Exp.complex-equivalent re≈ im≈

originalExpToSeriesAdd :
  (x y : Exp.BishopComplex) →
  toSeries (Exp._+C_ x y) ≡
  Algebra._+C_ (toSeries x) (toSeries y)
originalExpToSeriesAdd (Exp.complex a b) (Exp.complex c d) = refl

originalExpToSeriesSubtract :
  (x y : Exp.BishopComplex) →
  toSeries (Exp._-C_ x y) ≡
  Algebra._-C_ (toSeries x) (toSeries y)
originalExpToSeriesSubtract (Exp.complex a b) (Exp.complex c d) = refl

originalExpToSeriesMultiply :
  (x y : Exp.BishopComplex) →
  toSeries (Exp._*C_ x y) ≡
  Algebra._*C_ (toSeries x) (toSeries y)
originalExpToSeriesMultiply (Exp.complex a b) (Exp.complex c d) = refl

originalExpToSeriesZero :
  toSeries Exp.zeroC ≡ Algebra.zeroC
originalExpToSeriesZero = refl

originalExpToSeriesOne :
  toSeries Exp.oneC ≡ Algebra.oneC
originalExpToSeriesOne = refl

-- This is the ACTUAL Bishop power-series complex exponential,
-- transported unchanged into the native componentwise series carrier.
originalBishopExpOnSeries :
  Exp.BishopSetoidComplexTranscendentals →
  Series.BishopComplex → Series.BishopComplex
originalBishopExpOnSeries T z =
  toSeries (Exp.expC T (toExponential z))

originalBishopExpOnSeriesCongruent :
  (T : Exp.BishopSetoidComplexTranscendentals) →
  ∀ {x y : Series.BishopComplex} →
  Series._≈C_ x y →
  Series._≈C_
    (originalBishopExpOnSeries T x)
    (originalBishopExpOnSeries T y)
originalBishopExpOnSeriesCongruent T equivalent =
  originalExpEquivalenceToSeries
    (Exp.expCongruent T
      (originalSeriesEquivalenceToExp equivalent))

-- Compatibility with the source-valued exponential is definitional,
-- not a newly assumed identity between different analytic packages.
originalBishopExpSameSource :
  (T : Exp.BishopSetoidComplexTranscendentals) →
  (z : Exp.BishopComplex) →
  originalBishopExpOnSeries T (toSeries z) ≡
  toSeries (Exp.expC T z)
originalBishopExpSameSource T (Exp.complex a b) = refl
