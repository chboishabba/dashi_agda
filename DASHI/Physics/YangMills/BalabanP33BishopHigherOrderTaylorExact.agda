module DASHI.Physics.YangMills.BalabanP33BishopHigherOrderTaylorExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE
--
-- Zachary Murray,
-- "Constructive Analysis in the Agda Proof Assistant",
-- B.Sc. Honours thesis, Dalhousie University, 2022.
-- arXiv:2205.08354. No DOI assigned.
--
-- Code continuation: Viktor Csimma, `viktorcsimma/bishop`, pinned by DASHI.
--
-- DASHI CONTRIBUTION
--
-- Extend the already checked alternating sine/cosine interlacing by the two
-- additional truncations required by the inverse-dexp Bernoulli coefficient.
-- For every nonnegative point in the constructive half ball this proves
--
--   x - x^3/6 + x^5/120 - x^7/5040 <= sin x
--   sin x <= x - x^3/6 + x^5/120
--
-- and
--
--   1 - x^2/2 + x^4/24 - x^6/720 <= cos x
--   cos x <= 1 - x^2/2 + x^4/24.
--
-- These are literal index-two lower and index-one upper partial sums of the
-- Bishop series.  No analytic remainder estimate is supplied as a field.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised as ℚ using (ℚᵘ; _/_)
import Data.Rational.Unnormalised.Properties as ℚP

import Real as BishopReal
import RealProperties as BishopProperties

import DASHI.Foundations.BishopPowerSeriesElementaryBridgeExact as Elementary
import DASHI.Physics.YangMills.BalabanBishopConcreteSineCosineInterlacingExact as Concrete
import DASHI.Physics.YangMills.BalabanBishopFactorialPowerRecurrenceExact as Recurrence
import DASHI.Physics.YangMills.BalabanBishopAlternatingInterlacingFromDecreasingTermsExact as Alternating
import DASHI.Physics.YangMills.BalabanBishopAlternatingBracketFromMonotoneLimitsExact as Interlacing
import DASHI.Physics.YangMills.BalabanP33BishopLowOrderTaylorBracketsExact as Low
open import DASHI.Physics.YangMills.CompactLieProofLevel

oneTwentyFourth oneOneTwentieth oneSevenTwentieth oneFiveThousandFortieth : ℚᵘ
oneTwentyFourth = + 1 / 24
oneOneTwentieth = + 1 / 120
oneSevenTwentieth = + 1 / 720
oneFiveThousandFortieth = + 1 / 5040

four five six seven : Nat
four = suc (suc (suc (suc zero)))
five = suc four
six = suc five
seven = suc six

sineQuinticTerm sineSepticTerm cosineQuarticTerm cosineSexticTerm :
  BishopReal.ℝ → BishopReal.ℝ
sineQuinticTerm value =
  BishopReal._*_
    (BishopReal._⋆ oneOneTwentieth)
    (BishopReal.pow value five)
sineSepticTerm value =
  BishopReal._*_
    (BishopReal._⋆ oneFiveThousandFortieth)
    (BishopReal.pow value seven)
cosineQuarticTerm value =
  BishopReal._*_
    (BishopReal._⋆ oneTwentyFourth)
    (BishopReal.pow value four)
cosineSexticTerm value =
  BishopReal._*_
    (BishopReal._⋆ oneSevenTwentieth)
    (BishopReal.pow value six)

sineMagnitudeTwoEquivalentQuintic :
  ∀ value → BishopReal.NonNegative value →
  BishopReal._≃_
    (Recurrence.sineMagnitudeTerm value (suc (suc zero)))
    (sineQuinticTerm value)
sineMagnitudeTwoEquivalentQuintic value valueNonnegative =
  BishopProperties.*-cong
    (BishopProperties.⋆-cong ℚP.≃-refl)
    (Low.powerAbsoluteEquivalentPower value five valueNonnegative)

sineMagnitudeThreeEquivalentSeptic :
  ∀ value → BishopReal.NonNegative value →
  BishopReal._≃_
    (Recurrence.sineMagnitudeTerm value (suc (suc (suc zero))))
    (sineSepticTerm value)
sineMagnitudeThreeEquivalentSeptic value valueNonnegative =
  BishopProperties.*-cong
    (BishopProperties.⋆-cong ℚP.≃-refl)
    (Low.powerAbsoluteEquivalentPower value seven valueNonnegative)

cosineMagnitudeTwoEquivalentQuartic :
  ∀ value → BishopReal.NonNegative value →
  BishopReal._≃_
    (Recurrence.cosineMagnitudeTerm value (suc (suc zero)))
    (cosineQuarticTerm value)
cosineMagnitudeTwoEquivalentQuartic value valueNonnegative =
  BishopProperties.*-cong
    (BishopProperties.⋆-cong ℚP.≃-refl)
    (Low.powerAbsoluteEquivalentPower value four valueNonnegative)

cosineMagnitudeThreeEquivalentSextic :
  ∀ value → BishopReal.NonNegative value →
  BishopReal._≃_
    (Recurrence.cosineMagnitudeTerm value (suc (suc (suc zero))))
    (cosineSexticTerm value)
cosineMagnitudeThreeEquivalentSextic value valueNonnegative =
  BishopProperties.*-cong
    (BishopProperties.⋆-cong ℚP.≃-refl)
    (Low.powerAbsoluteEquivalentPower value six valueNonnegative)

upperOneEquivalentThreeMagnitudes :
  (dataSet : Alternating.AlternatingDecreasingSeriesData) →
  BishopReal._≃_
    (Alternating.upperPartial dataSet (suc zero))
    (BishopReal._+_
      (BishopReal._-_
        (Alternating.magnitude dataSet zero)
        (Alternating.magnitude dataSet (suc zero)))
      (Alternating.magnitude dataSet (suc (suc zero))))
upperOneEquivalentThreeMagnitudes dataSet =
  BishopProperties.≃-trans
    (Alternating.upperSuccessorExpansion dataSet zero)
    (BishopProperties.+-cong
      (BishopProperties.+-cong
        (Low.upperZeroEquivalentFirstMagnitude dataSet)
        (BishopProperties.-‿cong BishopProperties.≃-refl))
      BishopProperties.≃-refl)

lowerTwoEquivalentFourMagnitudes :
  (dataSet : Alternating.AlternatingDecreasingSeriesData) →
  BishopReal._≃_
    (Alternating.lowerPartial dataSet (suc (suc zero)))
    (BishopReal._+_
      (BishopReal._-_
        (Alternating.magnitude dataSet zero)
        (Alternating.magnitude dataSet (suc zero)))
      (BishopReal._-_
        (Alternating.magnitude dataSet (suc (suc zero)))
        (Alternating.magnitude dataSet (suc (suc (suc zero))))))
lowerTwoEquivalentFourMagnitudes dataSet =
  BishopProperties.≃-trans
    (Alternating.lowerSuccessorExpansion dataSet (suc zero))
    (BishopProperties.+-cong
      (Low.lowerOneEquivalentFirstMinusSecondMagnitude dataSet)
      BishopProperties.≃-refl)

record HigherOrderTaylorBounds
    (dataSet : Elementary.BishopElementaryPowerSeriesData)
    (value : BishopReal.ℝ) : Set₁ where
  field
    sineSepticLower :
      BishopReal._≤_
        (BishopReal._+_
          (BishopReal._-_ value (Low.sineCubicTerm value))
          (BishopReal._-_
            (sineQuinticTerm value)
            (sineSepticTerm value)))
        (Elementary.bishopSin dataSet value)

    sineQuinticUpper :
      BishopReal._≤_
        (Elementary.bishopSin dataSet value)
        (BishopReal._+_
          (BishopReal._-_ value (Low.sineCubicTerm value))
          (sineQuinticTerm value))

    cosineSexticLower :
      BishopReal._≤_
        (BishopReal._+_
          (BishopReal._-_
            BishopReal.1ℝ (Low.cosineQuadraticTerm value))
          (BishopReal._-_
            (cosineQuarticTerm value)
            (cosineSexticTerm value)))
        (Elementary.bishopCos dataSet value)

    cosineQuarticUpper :
      BishopReal._≤_
        (Elementary.bishopCos dataSet value)
        (BishopReal._+_
          (BishopReal._-_
            BishopReal.1ℝ (Low.cosineQuadraticTerm value))
          (cosineQuarticTerm value))

open HigherOrderTaylorBounds public

higherOrderTaylorBounds :
  ∀ {dataSet value} →
  Concrete.ConcreteHalfBallSeriesInputs dataSet value →
  HigherOrderTaylorBounds dataSet value
higherOrderTaylorBounds {dataSet} {value} inputs =
  let
    concrete = Concrete.concreteSineCosineInterlacing inputs
    sineData = Concrete.sineAlternatingSeriesData inputs
    cosineData = Concrete.cosineAlternatingSeriesData inputs
    sineInterlacing = Interlacing.sineInterlacing concrete
    cosineInterlacing = Interlacing.cosineInterlacing concrete
    valueNonnegative = Concrete.valueNonnegative inputs

    sineZero = Low.sineMagnitudeZeroEquivalentValue value valueNonnegative
    sineOne = Low.sineMagnitudeOneEquivalentCubic value valueNonnegative
    sineTwo = sineMagnitudeTwoEquivalentQuintic value valueNonnegative
    sineThree = sineMagnitudeThreeEquivalentSeptic value valueNonnegative

    cosineZero = Low.cosineMagnitudeZeroEquivalentOne value valueNonnegative
    cosineOne = Low.cosineMagnitudeOneEquivalentQuadratic value valueNonnegative
    cosineTwo = cosineMagnitudeTwoEquivalentQuartic value valueNonnegative
    cosineThree = cosineMagnitudeThreeEquivalentSextic value valueNonnegative

    sineUpperPolynomial :
      BishopReal._≃_
        (Alternating.upperPartial sineData (suc zero))
        (BishopReal._+_
          (BishopReal._-_ value (Low.sineCubicTerm value))
          (sineQuinticTerm value))
    sineUpperPolynomial =
      BishopProperties.≃-trans
        (upperOneEquivalentThreeMagnitudes sineData)
        (BishopProperties.+-cong
          (BishopProperties.+-cong sineZero
            (BishopProperties.-‿cong sineOne))
          sineTwo)

    sineLowerPolynomial :
      BishopReal._≃_
        (Alternating.lowerPartial sineData (suc (suc zero)))
        (BishopReal._+_
          (BishopReal._-_ value (Low.sineCubicTerm value))
          (BishopReal._-_
            (sineQuinticTerm value)
            (sineSepticTerm value)))
    sineLowerPolynomial =
      BishopProperties.≃-trans
        (lowerTwoEquivalentFourMagnitudes sineData)
        (BishopProperties.+-cong
          (BishopProperties.+-cong sineZero
            (BishopProperties.-‿cong sineOne))
          (BishopProperties.+-cong sineTwo
            (BishopProperties.-‿cong sineThree)))

    cosineUpperPolynomial :
      BishopReal._≃_
        (Alternating.upperPartial cosineData (suc zero))
        (BishopReal._+_
          (BishopReal._-_
            BishopReal.1ℝ (Low.cosineQuadraticTerm value))
          (cosineQuarticTerm value))
    cosineUpperPolynomial =
      BishopProperties.≃-trans
        (upperOneEquivalentThreeMagnitudes cosineData)
        (BishopProperties.+-cong
          (BishopProperties.+-cong cosineZero
            (BishopProperties.-‿cong cosineOne))
          cosineTwo)

    cosineLowerPolynomial :
      BishopReal._≃_
        (Alternating.lowerPartial cosineData (suc (suc zero)))
        (BishopReal._+_
          (BishopReal._-_
            BishopReal.1ℝ (Low.cosineQuadraticTerm value))
          (BishopReal._-_
            (cosineQuarticTerm value)
            (cosineSexticTerm value)))
    cosineLowerPolynomial =
      BishopProperties.≃-trans
        (lowerTwoEquivalentFourMagnitudes cosineData)
        (BishopProperties.+-cong
          (BishopProperties.+-cong cosineZero
            (BishopProperties.-‿cong cosineOne))
          (BishopProperties.+-cong cosineTwo
            (BishopProperties.-‿cong cosineThree)))
  in
  record
    { sineSepticLower =
        BishopProperties.≤-respˡ-≃
          (BishopProperties.≃-symm sineLowerPolynomial)
          (Interlacing.lowerPartialBelowRepresentedLimit
            sineInterlacing (suc (suc zero)))
    ; sineQuinticUpper =
        BishopProperties.≤-respʳ-≃ sineUpperPolynomial
          (Interlacing.representedLimitBelowUpperPartial
            sineInterlacing (suc zero))
    ; cosineSexticLower =
        BishopProperties.≤-respˡ-≃
          (BishopProperties.≃-symm cosineLowerPolynomial)
          (Interlacing.lowerPartialBelowRepresentedLimit
            cosineInterlacing (suc (suc zero)))
    ; cosineQuarticUpper =
        BishopProperties.≤-respʳ-≃ cosineUpperPolynomial
          (Interlacing.representedLimitBelowUpperPartial
            cosineInterlacing (suc zero))
    }

p33BishopHigherOrderTaylorLevel : ProofLevel
p33BishopHigherOrderTaylorLevel = machineChecked
