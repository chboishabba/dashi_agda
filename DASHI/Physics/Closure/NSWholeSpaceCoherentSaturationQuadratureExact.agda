module DASHI.Physics.Closure.NSWholeSpaceCoherentSaturationQuadratureExact where

------------------------------------------------------------------------
-- A / COHERENT SATURATION WITH CAUCHY PSD PRODUCED BY QUADRATURE
--
-- NSWholeSpaceCoherentSaturationReductionExact asks for
--
--   cauchyGramNonnegative.
--
-- The canonical whole-space route should not accept that as an independent
-- positivity authority.  Supply instead a literal weighted finite C^3 Cauchy
-- quadrature sequence converging to the selected continuous Cauchy Gram.
-- Finite PSD + Bishop order closure then produces positivity automatically.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import Real as BishopReal

import DASHI.Physics.Closure.NSTriadKNEuclideanViscousHeatRateExact as Heat
import DASHI.Physics.Closure.NSWholeSpaceCoherentSaturationReductionExact as Coherent
import DASHI.Physics.Closure.NSWholeSpaceBishopCauchyQuadratureLimitExact as Quadrature

record CoherentSaturationQuadratureData
    (fluid : Heat.PositiveViscosity)
    (point : Heat.PuncturedEuclideanFrequency) : Set₁ where
  constructor coherent-saturation-quadrature-data
  field
    commonGram cauchyGram centeredCorrection majorant : BishopReal.ℝ

    cauchyQuadrature :
      Quadrature.WeightedCauchyQuadratureApproximation cauchyGram

    majorantNonnegative :
      BishopReal.NonNegative majorant

    centeredSplit :
      BishopReal._≃_
        centeredCorrection
        (BishopReal._-_
          (BishopReal._*_
            (Coherent.outputInverse fluid point)
            commonGram)
          cauchyGram)

    coherentGramCarriesOutputSquare :
      BishopReal._≤_
        commonGram
        (BishopReal._*_
          (Heat.frequencyNormSquared (Heat.frequency point))
          majorant)

open CoherentSaturationQuadratureData public

toCoherentSaturationData :
  ∀ {fluid point} →
  CoherentSaturationQuadratureData fluid point →
  Coherent.CoherentSaturationData fluid point
toCoherentSaturationData D =
  Coherent.coherent-saturation-data
    (commonGram D)
    (cauchyGram D)
    (centeredCorrection D)
    (majorant D)
    (Quadrature.continuousWeightedCauchyGramNonnegative
      (cauchyQuadrature D))
    (majorantNonnegative D)
    (centeredSplit D)
    (coherentGramCarriesOutputSquare D)

coherentSaturationOriginBoundFromQuadrature :
  ∀ {fluid point} →
  (D : CoherentSaturationQuadratureData fluid point) →
  BishopReal._≤_
    (centeredCorrection D)
    (BishopReal._*_
      (Coherent.viscosityInverse fluid)
      (majorant D))
coherentSaturationOriginBoundFromQuadrature D =
  Coherent.coherentSaturationOriginBound
    (toCoherentSaturationData D)

cauchyPositivityProducedFromQuadrature : Bool
cauchyPositivityProducedFromQuadrature = true

freeContinuousCauchyPSDInputRequired : Bool
freeContinuousCauchyPSDInputRequired = false

remainingAnalyticInputIsQuadratureConvergence : Bool
remainingAnalyticInputIsQuadratureConvergence = true

pairwiseAbsoluteGramRequired : Bool
pairwiseAbsoluteGramRequired = false

clayPromotion : Bool
clayPromotion = false

cauchyPositivityProducedFromQuadratureIsTrue :
  cauchyPositivityProducedFromQuadrature ≡ true
cauchyPositivityProducedFromQuadratureIsTrue = refl

freeContinuousCauchyPSDInputRequiredIsFalse :
  freeContinuousCauchyPSDInputRequired ≡ false
freeContinuousCauchyPSDInputRequiredIsFalse = refl

remainingAnalyticInputIsQuadratureConvergenceIsTrue :
  remainingAnalyticInputIsQuadratureConvergence ≡ true
remainingAnalyticInputIsQuadratureConvergenceIsTrue = refl

pairwiseAbsoluteGramRequiredIsFalse :
  pairwiseAbsoluteGramRequired ≡ false
pairwiseAbsoluteGramRequiredIsFalse = refl

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
