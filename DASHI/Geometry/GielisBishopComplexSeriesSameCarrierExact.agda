{-# OPTIONS --safe #-}
module DASHI.Geometry.GielisBishopComplexSeriesSameCarrierExact where

------------------------------------------------------------------------
-- Pay the ORIGINAL two-BishopComplex-record same-carrier weld.
--
-- The original BishopComplexSeriesConvergenceExact and
-- BishopSetoidComplexExact have *distinct* Agda record types.
-- Both store the same vendored Bishop real components. Their
-- round-trip conversion is definitional, and their complex
-- + and * agree with the original BishopComplexAlgebraExact
-- operations, also definitionally.
--
-- This module transports the COMPLETED original componentwise
-- complex-series limit/convergence/uniqueness to the literal
-- BishopSetoidComplexExact carrier consumed by Gielis.
--
-- Not a conditional record with an unfilled 'identity' field:
-- equality of coordinates is proved by refl.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Product using (_,_)

import DASHI.Analysis.BishopComplexSeriesConvergenceExact as Series
import DASHI.Analysis.BishopComplexAlgebraExact as Algebra
import DASHI.Analysis.BishopSetoidComplexExact as Setoid

toSeries : Setoid.BishopComplex → Series.BishopComplex
toSeries (Setoid.complex a b) = Series.complex a b

toSetoid : Series.BishopComplex → Setoid.BishopComplex
toSetoid (Series.complex a b) = Setoid.complex a b

seriesRoundTrip : ∀ z → toSeries (toSetoid z) ≡ z
seriesRoundTrip (Series.complex a b) = refl

setoidRoundTrip : ∀ z → toSetoid (toSeries z) ≡ z
setoidRoundTrip (Setoid.complex a b) = refl

setoidPlusSameSeriesAlgebra : ∀ a b →
  toSeries (Setoid._+C_ a b)
  ≡ Algebra._+C_ (toSeries a) (toSeries b)
setoidPlusSameSeriesAlgebra
  (Setoid.complex a b) (Setoid.complex c d) = refl

setoidMultiplySameSeriesAlgebra : ∀ a b →
  toSeries (Setoid._*C_ a b)
  ≡ Algebra._*C_ (toSeries a) (toSeries b)
setoidMultiplySameSeriesAlgebra
  (Setoid.complex a b) (Setoid.complex c d) = refl

setoidUnitSameSeriesAlgebra :
  toSeries Setoid.oneC ≡ Algebra.oneC
setoidUnitSameSeriesAlgebra = refl

setoidZeroSameSeriesAlgebra :
  toSeries Setoid.zeroC ≡ Algebra.zeroC
setoidZeroSameSeriesAlgebra = refl

setoidEqualityToSeries : ∀ {a b} →
  Setoid._≈C_ a b → Series._≈C_ (toSeries a) (toSeries b)
setoidEqualityToSeries (Setoid.complex-equivalent re im) = re , im

seriesEqualityToSetoid : ∀ {a b} →
  Series._≈C_ a b →
  Setoid._≈C_ (toSetoid a) (toSetoid b)
seriesEqualityToSetoid (re , im) =
  Setoid.complex-equivalent re im

-- Explicit termwise transport into the original, already proven
-- series-limit owner. No new series convergence axiom is introduced.
toSeriesTerms :
  (Nat → Setoid.BishopComplex) → Nat → Series.BishopComplex
toSeriesTerms terms n = toSeries (terms n)

SetoidComponentwiseAbsolute :
  (Nat → Setoid.BishopComplex) → Set
SetoidComponentwiseAbsolute terms =
  Series.ComponentwiseAbsoluteSeriesConvergent (toSeriesTerms terms)

setoidComplexSeriesLimit :
  (terms : Nat → Setoid.BishopComplex) →
  SetoidComponentwiseAbsolute terms →
  Setoid.BishopComplex
setoidComplexSeriesLimit terms absolute =
  toSetoid (Series.complexSeriesLimit (toSeriesTerms terms) absolute)

-- This is the ORIGINAL componentwise convergence theorem,
-- transported to the Gielis complex record, not reimplemented.
setoidComplexSeriesLimitConverges :
  ∀ terms (absolute : SetoidComponentwiseAbsolute terms) →
  Series.ComplexSeriesConvergesTo
    (toSeriesTerms terms)
    (toSeries (setoidComplexSeriesLimit terms absolute))
setoidComplexSeriesLimitConverges terms absolute =
  Series.complexSeriesLimitConvergence
    (toSeriesTerms terms) absolute

setoidComplexSeriesLimitUnique :
  ∀ terms (absolute : SetoidComponentwiseAbsolute terms)
    (other : Setoid.BishopComplex) →
  Series.ComplexSeriesConvergesTo
    (toSeriesTerms terms) (toSeries other) →
  Setoid._≈C_
    (setoidComplexSeriesLimit terms absolute)
    other
setoidComplexSeriesLimitUnique terms absolute other convergence =
  seriesEqualityToSetoid
    (Series.complexSeriesLimitUnique
      (toSeriesTerms terms)
      absolute
      (toSeries other)
      convergence)

-- Remaining: identify the *specific* original factorial
-- imaginary-axis terms with the Round11 configured sine/cosine
-- functions, prove absolute convergence of their two parts,
-- and establish the complex Cauchy-product identity. This file
-- deliberately does not pretend that the generic SERIES owner
-- provided those *specific* inputs.
