module DASHI.Physics.Closure.NSAncientLocalizedPoincareFluxScalingNoGoExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Luis Caffarelli; Robert Kohn; Louis Nirenberg.
-- Title: "Partial regularity of suitable weak solutions of the
--         Navier-Stokes equations".
-- DOI: 10.1002/cpa.3160350604.
--
-- Authors: Tobias Barker; Christophe Prange.
-- Title: "Quantitative Regularity for the Navier-Stokes Equations Via
--         Spatial Concentration".
-- DOI: 10.1007/s00220-021-04122-x.
--
-- ROUND65 / R2 LOCALIZED-ENERGY SCALING OBSTRUCTION
--
-- A localized Poincare argument on a ball/cube of radius R has the
-- dimensional damping scale
--
--   damping ~ nu A^2 R,
--
-- while both the absolute advective boundary flux and the absolute pressure
-- boundary flux (at the natural p ~ A^2 scale) have critical scale
--
--   flux ~ A^3 R^2.
--
-- Their ratio is the local Reynolds factor A R / nu.  Consequently a bounded
-- ancient velocity with merely A <= K does NOT make absolute large-radius
-- boundary flux small relative to localized Poincare damping.
--
-- The main theorem below is exact and coefficient-free:
--
--   theta*nu < A*R  and A,R > 0
--     => not (A^3 R^2 <= theta * nu A^2 R).
--
-- Thus a positive R2 oscillation contraction must use cancellation, decay,
-- pressure structure, or another genuinely scale-improving property of the
-- blow-up class.  Absolute boundedness estimates cannot supply it.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _*_; _≤_; _<_; Positive; positive; NonNegative; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst₂)
open import Relation.Nullary.Negation.Core using (¬_)

square : ℚ → ℚ
square x = x * x

localizedPoincareDampingScale : ℚ → ℚ → ℚ → ℚ
localizedPoincareDampingScale nu amplitude radius =
  nu * square amplitude * radius

absoluteTransportFluxScale : ℚ → ℚ → ℚ
absoluteTransportFluxScale amplitude radius =
  amplitude * square amplitude * square radius

absolutePressureFluxScale : ℚ → ℚ → ℚ
absolutePressureFluxScale amplitude radius =
  amplitude * square amplitude * square radius

localReynoldsNumerator : ℚ → ℚ → ℚ
localReynoldsNumerator amplitude radius = amplitude * radius

transportAndPressureHaveSameCriticalScale :
  (amplitude radius : ℚ) →
  absoluteTransportFluxScale amplitude radius
  ≡ absolutePressureFluxScale amplitude radius
transportAndPressureHaveSameCriticalScale amplitude radius = solve (amplitude ∷ radius ∷ [])

unitViscosityFluxIsReynoldsTimesDamping :
  (amplitude radius : ℚ) →
  absoluteTransportFluxScale amplitude radius
  ≡ localReynoldsNumerator amplitude radius
    * localizedPoincareDampingScale 1ℚ amplitude radius
unitViscosityFluxIsReynoldsTimesDamping amplitude radius =
  solve (amplitude ∷ radius ∷ [])

positiveQuadraticRadiusBase :
  (amplitude radius : ℚ) →
  0ℚ < amplitude →
  0ℚ < radius →
  0ℚ < square amplitude * radius
positiveQuadraticRadiusBase amplitude radius amplitudePositive radiusPositive =
  let
    squarePositive : 0ℚ < square amplitude
    squarePositive =
      let instance amplitudePos : Positive amplitude
          amplitudePos = positive amplitudePositive
      in ℚP.*-monoʳ-<-pos amplitude amplitudePositive

    instance radiusPos : Positive radius
        radiusPos = positive radiusPositive
  in
  ℚP.*-monoʳ-<-pos radius squarePositive

fixedRelativeAbsorptionFailsAboveLocalReynoldsThreshold :
  (theta nu amplitude radius : ℚ) →
  0ℚ < amplitude →
  0ℚ < radius →
  theta * nu < amplitude * radius →
  ¬ (absoluteTransportFluxScale amplitude radius
      ≤ theta * localizedPoincareDampingScale nu amplitude radius)
fixedRelativeAbsorptionFailsAboveLocalReynoldsThreshold
    theta nu amplitude radius amplitudePositive radiusPositive reynoldsAbove proposed =
  let
    base = square amplitude * radius

    basePositive : 0ℚ < base
    basePositive = positiveQuadraticRadiusBase amplitude radius amplitudePositive radiusPositive

    instance basePos : Positive base
        basePos = positive basePositive

    scaledStrict : (theta * nu) * base < (amplitude * radius) * base
    scaledStrict = ℚP.*-monoʳ-<-pos base reynoldsAbove

    scaledStrictNormalized :
      theta * localizedPoincareDampingScale nu amplitude radius
      < absoluteTransportFluxScale amplitude radius
    scaledStrictNormalized =
      subst₂ _<_
        (solve (theta ∷ nu ∷ amplitude ∷ radius ∷ []))
        (solve (amplitude ∷ radius ∷ []))
        scaledStrict
  in
  ℚP.<-irrefl
    (absoluteTransportFluxScale amplitude radius)
    (ℚP.≤-<-trans proposed scaledStrictNormalized)

unitAmplitudeDamping :
  (radius : ℚ) →
  localizedPoincareDampingScale 1ℚ 1ℚ radius ≡ radius
unitAmplitudeDamping radius = solve (radius ∷ [])

unitAmplitudeFlux :
  (radius : ℚ) →
  absoluteTransportFluxScale 1ℚ radius ≡ square radius
unitAmplitudeFlux radius = solve (radius ∷ [])

fixedContractionCoefficientFailsAtLargeRadius :
  (theta radius : ℚ) →
  0ℚ < radius →
  theta < radius →
  ¬ (absoluteTransportFluxScale 1ℚ radius
      ≤ theta * localizedPoincareDampingScale 1ℚ 1ℚ radius)
fixedContractionCoefficientFailsAtLargeRadius theta radius radiusPositive thetaBelowRadius =
  fixedRelativeAbsorptionFailsAboveLocalReynoldsThreshold
    theta 1ℚ 1ℚ radius
    (ℚP.<⇒≱ (ℚP.≤-refl {x = 1ℚ}))
    radiusPositive
    (subst₂ _<_ (solve (theta ∷ [])) (solve (radius ∷ [])) thetaBelowRadius)
