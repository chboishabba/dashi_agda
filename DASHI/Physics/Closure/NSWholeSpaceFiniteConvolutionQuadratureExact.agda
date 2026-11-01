module DASHI.Physics.Closure.NSWholeSpaceFiniteConvolutionQuadratureExact where

------------------------------------------------------------------------
-- A / EXACT FINITE CONVOLUTION QUADRATURE FACTORISATION
--
-- A continuum Fubini theorem is not needed at the finite approximation layer.
-- Let e_i be a finite energy quadrature and, for every outer index i, let
-- shifted_i(j) represent the same quadrature sampled at the translated
-- convolution coordinate xi_j - eta_i.
--
-- If the chosen finite quadrature is translation-reindexed exactly,
--
--   sum_j shifted_i(j) ~= sum_j e_j,
--
-- then native Bishop finite-sum extensionality plus the existing finite
-- rectangle product theorem give
--
--   sum_i e_i (sum_j shifted_i(j))
--      ~= (sum_i e_i)^2.
--
-- This is the exact finite Fubini/translation theorem required by
-- NSWholeSpaceConvolutionQuadratureCompletionExact.  No measure, sigma algebra,
-- improper integral, dominated convergence or continuum Fubini authority is
-- used here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import Real as BishopReal
import RealProperties as BishopP
import Sequence as BishopSequence

import DASHI.Foundations.BishopFiniteSeriesExtensionalityExact as Ext
import DASHI.Foundations.BishopFiniteSeriesRectangleProductExact as Rect

record FiniteTranslationReindexedConvolutionQuadrature : Set₁ where
  constructor finite-translation-reindexed-convolution-quadrature
  field
    energy : Nat → BishopReal.ℝ
    shiftedEnergy : Nat → Nat → BishopReal.ℝ
    count : Nat

    translatedInnerSumExact :
      (outer : Nat) →
      BishopReal._≃_
        (BishopSequence.SeriesOf (shiftedEnergy outer) count)
        (BishopSequence.SeriesOf energy count)

open FiniteTranslationReindexedConvolutionQuadrature public

energyMass :
  FiniteTranslationReindexedConvolutionQuadrature →
  BishopReal.ℝ
energyMass Q =
  BishopSequence.SeriesOf (energy Q) (count Q)

convolutionRow :
  (Q : FiniteTranslationReindexedConvolutionQuadrature) →
  Nat → BishopReal.ℝ
convolutionRow Q outer =
  BishopReal._*_
    (energy Q outer)
    (BishopSequence.SeriesOf (shiftedEnergy Q outer) (count Q))

convolutionMass :
  FiniteTranslationReindexedConvolutionQuadrature →
  BishopReal.ℝ
convolutionMass Q =
  BishopSequence.SeriesOf (convolutionRow Q) (count Q)

rowBecomesRectangleRow :
  (Q : FiniteTranslationReindexedConvolutionQuadrature) →
  (outer : Nat) →
  BishopReal._≃_
    (convolutionRow Q outer)
    (Rect.rectangleRow (energy Q) (energy Q) outer (count Q))
rowBecomesRectangleRow Q outer =
  BishopP.*-congˡ
    (translatedInnerSumExact Q outer)

convolutionMassIsEnergyRectangle :
  (Q : FiniteTranslationReindexedConvolutionQuadrature) →
  BishopReal._≃_
    (convolutionMass Q)
    (Rect.rectangleSum
      (energy Q) (energy Q)
      (count Q) (count Q))
convolutionMassIsEnergyRectangle Q =
  Ext.seriesPartialSumsCongruent
    (rowBecomesRectangleRow Q)
    (count Q)

finiteConvolutionFactorisation :
  (Q : FiniteTranslationReindexedConvolutionQuadrature) →
  BishopReal._≃_
    (convolutionMass Q)
    (BishopReal._*_
      (energyMass Q)
      (energyMass Q))
finiteConvolutionFactorisation Q =
  BishopP.≃-trans
    (convolutionMassIsEnergyRectangle Q)
    (Rect.rectangleProduct
      (energy Q) (energy Q)
      (count Q) (count Q))

finiteFubiniIsPureFiniteAlgebra : Bool
finiteFubiniIsPureFiniteAlgebra = true

finiteTranslationReindexingIsOnlyGeometricInput : Bool
finiteTranslationReindexingIsOnlyGeometricInput = true

continuumMeasureTheoryUsed : Bool
continuumMeasureTheoryUsed = false

finiteConvolutionFactorisationClosed : Bool
finiteConvolutionFactorisationClosed = true

clayPromotion : Bool
clayPromotion = false

finiteFubiniIsPureFiniteAlgebraIsTrue :
  finiteFubiniIsPureFiniteAlgebra ≡ true
finiteFubiniIsPureFiniteAlgebraIsTrue = refl

finiteTranslationReindexingIsOnlyGeometricInputIsTrue :
  finiteTranslationReindexingIsOnlyGeometricInput ≡ true
finiteTranslationReindexingIsOnlyGeometricInputIsTrue = refl

continuumMeasureTheoryUsedIsFalse :
  continuumMeasureTheoryUsed ≡ false
continuumMeasureTheoryUsedIsFalse = refl

finiteConvolutionFactorisationClosedIsTrue :
  finiteConvolutionFactorisationClosed ≡ true
finiteConvolutionFactorisationClosedIsTrue = refl

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
