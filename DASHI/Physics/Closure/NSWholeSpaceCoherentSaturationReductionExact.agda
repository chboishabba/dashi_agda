module DASHI.Physics.Closure.NSWholeSpaceCoherentSaturationReductionExact where

------------------------------------------------------------------------
-- A / COHERENT SATURATION REDUCTION
--
-- Pairwise positive majorisation is the wrong operation on the continuous
-- same-output pair carrier: it destroys Gram coherence and introduces an
-- additional free integration variable.
--
-- Keep the pair sum/integral signed.  The centered coefficient identity is
--
--   s/[a(a+s)] = 1/a - 1/(a+s).
--
-- Therefore, AFTER coherent aggregation,
--
--   C_centered
--      = a^{-1} G_common - G_Cauchy.
--
-- The Cauchy/resolvent Gram is positive semidefinite (finite B: R446/R447;
-- continuous A: separate analytic producer).  Hence
--
--   C_centered <= a^{-1} G_common.
--
-- If the coherent projected convolution Gram obeys
--
--   G_common <= |xi|^2 M,
--
-- then a = nu |xi|^2 gives
--
--   C_centered <= nu^{-1} M.
--
-- This owner proves exactly that ordered-field reduction on Bishop reals.  It
-- does NOT replace the signed pair Gram by |Gram| and it does NOT require a
-- pairwise positive majorant.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import Inverse as BishopInverse
import Real as BishopReal
import RealProperties as BishopP

import DASHI.Foundations.BishopGeometricReciprocalSquareFromCrossExact as Reciprocal
import DASHI.Physics.Closure.NSTriadKNEuclideanViscousHeatRateExact as Heat
import DASHI.Physics.Closure.NSWholeSpaceR3RadialOriginCancellationExact as R3

record CoherentSaturationData
    (fluid : Heat.PositiveViscosity)
    (point : Heat.PuncturedEuclideanFrequency) : Set₁ where
  constructor coherent-saturation-data
  field
    commonGram cauchyGram centeredCorrection majorant : BishopReal.ℝ

    cauchyGramNonnegative :
      BishopReal.NonNegative cauchyGram

    majorantNonnegative :
      BishopReal.NonNegative majorant

    centeredSplit :
      BishopReal._≃_
        centeredCorrection
        (BishopReal._-_
          (BishopReal._*_
            (BishopInverse._⁻¹
              (Heat.viscousHeatRate fluid (Heat.frequency point))
              (Reciprocal.xNonzero
                (Heat.viscousHeatRatePositive fluid point)))
            commonGram)
          cauchyGram)

    coherentGramCarriesOutputSquare :
      BishopReal._≤_
        commonGram
        (BishopReal._*_
          (Heat.frequencyNormSquared (Heat.frequency point))
          majorant)

open CoherentSaturationData public

outputInverse :
  (fluid : Heat.PositiveViscosity) →
  (point : Heat.PuncturedEuclideanFrequency) →
  BishopReal.ℝ
outputInverse fluid point =
  BishopInverse._⁻¹
    (Heat.viscousHeatRate fluid (Heat.frequency point))
    (Reciprocal.xNonzero
      (Heat.viscousHeatRatePositive fluid point))

outputInverseNonnegative :
  (fluid : Heat.PositiveViscosity) →
  (point : Heat.PuncturedEuclideanFrequency) →
  BishopReal.NonNegative (outputInverse fluid point)
outputInverseNonnegative fluid point =
  BishopP.pos⇒nonNeg
    (BishopInverse.posx⇒posx⁻¹
      (Reciprocal.xNonzero
        (Heat.viscousHeatRatePositive fluid point))
      (BishopP.0<x⇒posx
        (Heat.viscousHeatRatePositive fluid point)))

subtractNonnegativeBelowLeft :
  (left right : BishopReal.ℝ) →
  BishopReal.NonNegative right →
  BishopReal._≤_
    (BishopReal._-_ left right)
    left
subtractNonnegativeBelowLeft left right rightNN =
  let
    zeroBelowRight = BishopP.nonNegx⇒0≤x rightNN
    negRightBelowZero =
      BishopP.neg-mono-≤ zeroBelowRight
    shifted =
      BishopP.+-monoʳ-≤ left negRightBelowZero
  in
  BishopP.≤-respˡ-≃
    (let open BishopP.ℝ-Solver
     in solve 2
       (λ l r → l ⊖ r ⊜ l ⊕ (⊝ r))
       BishopP.≃-refl left right)
    (BishopP.≤-respʳ-≃
      (BishopP.+-identityʳ left)
      shifted)

centeredCorrectionBelowCommonResolventGram :
  ∀ {fluid point} →
  (D : CoherentSaturationData fluid point) →
  BishopReal._≤_
    (centeredCorrection D)
    (BishopReal._*_
      (outputInverse fluid point)
      (commonGram D))
centeredCorrectionBelowCommonResolventGram {fluid} {point} D =
  BishopP.≤-respˡ-≃
    (centeredSplit D)
    (subtractNonnegativeBelowLeft
      (BishopReal._*_
        (outputInverse fluid point)
        (commonGram D))
      (cauchyGram D)
      (cauchyGramNonnegative D))

coherentGramScaledByOutputInverse :
  ∀ {fluid point} →
  (D : CoherentSaturationData fluid point) →
  BishopReal._≤_
    (BishopReal._*_
      (outputInverse fluid point)
      (commonGram D))
    (BishopReal._*_
      (outputInverse fluid point)
      (BishopReal._*_
        (Heat.frequencyNormSquared (Heat.frequency point))
        (majorant D)))
coherentGramScaledByOutputInverse {fluid} {point} D =
  BishopP.*-monoˡ-≤-nonNeg
    (coherentGramCarriesOutputSquare D)
    (outputInverseNonnegative fluid point)

viscosityInverse :
  Heat.PositiveViscosity → BishopReal.ℝ
viscosityInverse fluid =
  BishopInverse._⁻¹
    (Heat.viscosity fluid)
    (Reciprocal.xNonzero (Heat.viscosityPositive fluid))

outputInverseTimesOutputSquare :
  (fluid : Heat.PositiveViscosity) →
  (point : Heat.PuncturedEuclideanFrequency) →
  BishopReal._≃_
    (BishopReal._*_
      (outputInverse fluid point)
      (Heat.frequencyNormSquared (Heat.frequency point)))
    (viscosityInverse fluid)
outputInverseTimesOutputSquare fluid point =
  let
    rate =
      R3.positive-viscosity-radius-square
        (Heat.viscosity fluid)
        (Heat.frequencyNormSquared (Heat.frequency point))
        (Heat.viscosityPositive fluid)
        (Heat.normSquaredPositive point)

    productInverse = R3.inverseProductExact rate
    q = Heat.frequencyNormSquared (Heat.frequency point)
    iq =
      BishopInverse._⁻¹ q
        (R3.radiusSquaredNonzero rate)
    qLaw =
      BishopInverse.*-inverseˡ q
        (R3.radiusSquaredNonzero rate)

    open BishopP.ℝ-Solver
  in
  BishopP.≃-trans
    (BishopP.*-congˡ productInverse)
    (BishopP.≃-trans
      (solve 3
        (λ n q' iq' →
          (n ⊗ iq') ⊗ q'
          ⊜ n ⊗ (iq' ⊗ q'))
        BishopP.≃-refl
        (viscosityInverse fluid) q iq)
      (BishopP.≃-trans
        (BishopP.*-congˡ qLaw)
        (BishopP.*-identityʳ
          (viscosityInverse fluid))))

coherentSaturationOriginBound :
  ∀ {fluid point} →
  (D : CoherentSaturationData fluid point) →
  BishopReal._≤_
    (centeredCorrection D)
    (BishopReal._*_
      (viscosityInverse fluid)
      (majorant D))
coherentSaturationOriginBound {fluid} {point} D =
  BishopP.≤-trans
    (centeredCorrectionBelowCommonResolventGram D)
    (BishopP.≤-trans
      (coherentGramScaledByOutputInverse D)
      (BishopP.≤-respʳ-≃
        (BishopP.*-congʳ
          (outputInverseTimesOutputSquare fluid point))
        BishopP.≤-refl))

coherentSaturationReductionClosed : Bool
coherentSaturationReductionClosed = true

pairwiseAbsoluteGramRequired : Bool
pairwiseAbsoluteGramRequired = false

pairwisePositiveMajorantRequired : Bool
pairwisePositiveMajorantRequired = false

continuousCauchyPSDProvedHere : Bool
continuousCauchyPSDProvedHere = false

clayPromotion : Bool
clayPromotion = false

coherentSaturationReductionClosedIsTrue :
  coherentSaturationReductionClosed ≡ true
coherentSaturationReductionClosedIsTrue = refl

pairwiseAbsoluteGramRequiredIsFalse :
  pairwiseAbsoluteGramRequired ≡ false
pairwiseAbsoluteGramRequiredIsFalse = refl

pairwisePositiveMajorantRequiredIsFalse :
  pairwisePositiveMajorantRequired ≡ false
pairwisePositiveMajorantRequiredIsFalse = refl

continuousCauchyPSDProvedHereIsFalse :
  continuousCauchyPSDProvedHere ≡ false
continuousCauchyPSDProvedHereIsFalse = refl

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
