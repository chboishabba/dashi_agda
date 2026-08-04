module DASHI.Physics.YangMills.BalabanP33BishopInverseDexpCoefficientExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Brian C. Hall,
-- "Lie Groups, Lie Algebras, and Representations: An Elementary
-- Introduction", second edition, Springer, 2015.
-- DOI: 10.1007/978-3-319-13467-3.
--
-- Ethan Eade,
-- "Derivative of the Exponential Map", technical note, 2018 revision.
-- No DOI recorded.
--
-- Zachary Murray,
-- "Constructive Analysis in the Agda Proof Assistant",
-- B.Sc. Honours thesis, Dalhousie University, 2022.
-- arXiv:2205.08354. No DOI assigned.
--
-- DASHI CONTRIBUTION
--
-- Close the removable-singularity part of the inverse-dexp coefficient without
-- dividing constructive reals. Put
--
--   n(t) = 2 sin t - t(1+cos t),
--   d(t) = 2 t^2 sin t.
--
-- On the nonnegative half ball this module proves the cross-multiplied bounds
--
--   (1/12) d(t) <= n(t) <= (1/6) d(t).
--
-- For t>0, d(t)>0 and ordinary positive-denominator cancellation therefore
-- gives 1/12 <= beta(t) <= 1/6. The proof uses the exact gaps
--
--   lower - (t^2/6) sine-upper
--     = t^5 [47/20160 + (1/560)(1/4-t^2)],
--
--   (t^2/3) sine-lower - upper
--     = t^3 [1831/11520
--              + (11/360)(1/4-t^2)
--              + (1/720)(1/16-t^4)].
------------------------------------------------------------------------

open import Data.Integer.Base using (+_; nonNeg)
open import Data.Rational.Unnormalised as ℚ using (ℚᵘ; 0ℚᵘ; _/_)
import Data.Rational.Unnormalised.Properties as ℚP

import Real as BishopReal
import RealProperties as BishopProperties

import DASHI.Foundations.BishopPowerSeriesElementaryBridgeExact as Elementary
import DASHI.Physics.YangMills.BalabanClayGate4BishopHalfRadiusRealEstimatesExact as Estimates
import DASHI.Physics.YangMills.BalabanBishopConcreteSineCosineInterlacingExact as Concrete
import DASHI.Physics.YangMills.BalabanP33BishopTaylorPolynomialFormExact as Low
import DASHI.Physics.YangMills.BalabanP33BishopHigherOrderTaylorExact as Higher
import DASHI.Physics.YangMills.BalabanP33BishopInverseDexpNumeratorExact as Numerator
open import DASHI.Physics.YangMills.CompactLieProofLevel

oneTwelfth oneSixth oneThird oneQuarter oneSixteenth : ℚᵘ
oneTwelfth = + 1 / 12
oneSixth = + 1 / 6
oneThird = + 1 / 3
oneQuarter = + 1 / 4
oneSixteenth = + 1 / 16

oneFiveSixtieth elevenThreeSixtieth oneSevenTwentieth : ℚᵘ
oneFiveSixtieth = + 1 / 560
elevenThreeSixtieth = + 11 / 360
oneSevenTwentieth = + 1 / 720

fortySevenTwentyOneSixtieth eighteenThirtyOneElevenFiveTwenty : ℚᵘ
fortySevenTwentyOneSixtieth = + 47 / 20160
eighteenThirtyOneElevenFiveTwenty = + 1831 / 11520

embed : ℚᵘ → BishopReal.ℝ
embed = BishopReal._⋆

square cube fourth fifth : BishopReal.ℝ → BishopReal.ℝ
square value = BishopReal._*_ value value
cube value = BishopReal._*_ (square value) value
fourth value = BishopReal._*_ (square value) (square value)
fifth value = BishopReal._*_ (fourth value) value

embeddedRationalNonnegative :
  ∀ rational → ℚ.NonNegative rational →
  BishopReal.NonNegative (embed rational)
embeddedRationalNonnegative rational rationalNonnegative =
  BishopProperties.0≤x⇒nonNegx
    (BishopProperties.p≤q⇒p⋆≤q⋆
      0ℚᵘ rational
      (ℚP.nonNegative⁻¹ rational
        ⦃ rationalNonnegative ⦄))

oneSixthNonnegative : BishopReal.NonNegative (embed oneSixth)
oneSixthNonnegative = embeddedRationalNonnegative oneSixth nonNeg
oneThirdNonnegative : BishopReal.NonNegative (embed oneThird)
oneThirdNonnegative = embeddedRationalNonnegative oneThird nonNeg
oneFiveSixtiethNonnegative : BishopReal.NonNegative (embed oneFiveSixtieth)
oneFiveSixtiethNonnegative =
  embeddedRationalNonnegative oneFiveSixtieth nonNeg
elevenThreeSixtiethNonnegative :
  BishopReal.NonNegative (embed elevenThreeSixtieth)
elevenThreeSixtiethNonnegative =
  embeddedRationalNonnegative elevenThreeSixtieth nonNeg
oneSevenTwentiethNonnegative :
  BishopReal.NonNegative (embed oneSevenTwentieth)
oneSevenTwentiethNonnegative =
  embeddedRationalNonnegative oneSevenTwentieth nonNeg
fortySevenPositive :
  BishopReal.NonNegative (embed fortySevenTwentyOneSixtieth)
fortySevenPositive =
  embeddedRationalNonnegative fortySevenTwentyOneSixtieth nonNeg
eighteenThirtyOnePositive :
  BishopReal.NonNegative (embed eighteenThirtyOneElevenFiveTwenty)
eighteenThirtyOnePositive =
  embeddedRationalNonnegative eighteenThirtyOneElevenFiveTwenty nonNeg

nonnegativeDifferenceGivesOrder :
  ∀ {left right} →
  BishopReal._≤_ BishopReal.0ℝ (BishopReal._-_ right left) →
  BishopReal._≤_ left right
nonnegativeDifferenceGivesOrder {left} {right} differenceNonnegative =
  BishopProperties.≤-respʳ-≃
    (let open BishopProperties.ℝ-Solver
     in solve 2
        (λ l r → l ⊕ (r ⊖ l) ⊜ r)
        BishopProperties.≃-refl left right)
    (BishopProperties.≤-respˡ-≃
      (BishopProperties.≃-symm
        (BishopProperties.+-identityʳ left))
      (BishopProperties.+-monoʳ-≤ left differenceNonnegative))

squareNonnegativeFromInput :
  ∀ value → BishopReal.NonNegative value →
  BishopReal.NonNegative (square value)
squareNonnegativeFromInput value valueNonnegative =
  BishopProperties.nonNegx,y⇒nonNegx*y valueNonnegative valueNonnegative

cubeNonnegative :
  ∀ value → BishopReal.NonNegative value →
  BishopReal.NonNegative (cube value)
cubeNonnegative value valueNonnegative =
  BishopProperties.nonNegx,y⇒nonNegx*y
    (squareNonnegativeFromInput value valueNonnegative)
    valueNonnegative

fourthNonnegative :
  ∀ value → BishopReal.NonNegative value →
  BishopReal.NonNegative (fourth value)
fourthNonnegative value valueNonnegative =
  BishopProperties.nonNegx,y⇒nonNegx*y
    (squareNonnegativeFromInput value valueNonnegative)
    (squareNonnegativeFromInput value valueNonnegative)

fifthNonnegative :
  ∀ value → BishopReal.NonNegative value →
  BishopReal.NonNegative (fifth value)
fifthNonnegative value valueNonnegative =
  BishopProperties.nonNegx,y⇒nonNegx*y
    (fourthNonnegative value valueNonnegative)
    valueNonnegative

squareBelowQuarter :
  ∀ {dataSet value} →
  Concrete.ConcreteHalfBallSeriesInputs dataSet value →
  BishopReal._≤_ (square value) (embed oneQuarter)
squareBelowQuarter inputs =
  Estimates.halfBallSquareBelowQuarterProof
    (Concrete.insideHalf inputs)

squareGapNonnegative :
  ∀ {dataSet value} →
  Concrete.ConcreteHalfBallSeriesInputs dataSet value →
  BishopReal.NonNegative
    (BishopReal._-_ (embed oneQuarter) (square value))
squareGapNonnegative inputs =
  BishopProperties.0≤x⇒nonNegx
    (Low.orderGivesNonnegativeDifference (squareBelowQuarter inputs))

fourthBelowSixteenth :
  ∀ {dataSet value} →
  Concrete.ConcreteHalfBallSeriesInputs dataSet value →
  BishopReal._≤_ (fourth value) (embed oneSixteenth)
fourthBelowSixteenth {value = value} inputs =
  BishopProperties.≤-respʳ-≃
    (BishopProperties.≃-symm
      (BishopProperties.⋆-distrib-* oneQuarter oneQuarter))
    (BishopProperties.*-mono-≤
      (squareNonnegativeFromInput value
        (Concrete.valueNonnegative inputs))
      (squareNonnegativeFromInput value
        (Concrete.valueNonnegative inputs))
      (squareBelowQuarter inputs)
      (squareBelowQuarter inputs))

fourthGapNonnegative :
  ∀ {dataSet value} →
  Concrete.ConcreteHalfBallSeriesInputs dataSet value →
  BishopReal.NonNegative
    (BishopReal._-_ (embed oneSixteenth) (fourth value))
fourthGapNonnegative inputs =
  BishopProperties.0≤x⇒nonNegx
    (Low.orderGivesNonnegativeDifference (fourthBelowSixteenth inputs))

lowerGapFactor : BishopReal.ℝ → BishopReal.ℝ
lowerGapFactor value =
  BishopReal._+_
    (embed fortySevenTwentyOneSixtieth)
    (BishopReal._*_
      (embed oneFiveSixtieth)
      (BishopReal._-_ (embed oneQuarter) (square value)))

upperGapFactor : BishopReal.ℝ → BishopReal.ℝ
upperGapFactor value =
  BishopReal._+_
    (embed eighteenThirtyOneElevenFiveTwenty)
    (BishopReal._+_
      (BishopReal._*_
        (embed elevenThreeSixtieth)
        (BishopReal._-_ (embed oneQuarter) (square value)))
      (BishopReal._*_
        (embed oneSevenTwentieth)
        (BishopReal._-_ (embed oneSixteenth) (fourth value))))

lowerGapFactorNonnegative :
  ∀ {dataSet value} →
  Concrete.ConcreteHalfBallSeriesInputs dataSet value →
  BishopReal.NonNegative (lowerGapFactor value)
lowerGapFactorNonnegative inputs =
  BishopProperties.nonNegx,y⇒nonNegx+y
    fortySevenPositive
    (BishopProperties.nonNegx,y⇒nonNegx*y
      oneFiveSixtiethNonnegative
      (squareGapNonnegative inputs))

upperGapFactorNonnegative :
  ∀ {dataSet value} →
  Concrete.ConcreteHalfBallSeriesInputs dataSet value →
  BishopReal.NonNegative (upperGapFactor value)
upperGapFactorNonnegative inputs =
  BishopProperties.nonNegx,y⇒nonNegx+y
    eighteenThirtyOnePositive
    (BishopProperties.nonNegx,y⇒nonNegx+y
      (BishopProperties.nonNegx,y⇒nonNegx*y
        elevenThreeSixtiethNonnegative
        (squareGapNonnegative inputs))
      (BishopProperties.nonNegx,y⇒nonNegx*y
        oneSevenTwentiethNonnegative
        (fourthGapNonnegative inputs)))

lowerCoefficientPolynomialIdentity : ∀ value →
  BishopReal._≃_
    (BishopReal._-_
      (Numerator.inverseDexpNumeratorLowerEnvelope value)
      (BishopReal._*_
        (embed oneSixth)
        (BishopReal._*_
          (square value)
          (Numerator.sineQuinticUpperPolynomial value))))
    (BishopReal._*_ (fifth value) (lowerGapFactor value))
lowerCoefficientPolynomialIdentity value =
  let open BishopProperties.ℝ-Solver
  in solve 1
    (λ t →
      ((Κ (+ 2 / 1) ⊗
          ((t ⊖ (Κ (+ 1 / 6) ⊗ ((t ⊗ t) ⊗ t)))
            ⊕ ((Κ (+ 1 / 120) ⊗
                  ((((t ⊗ t) ⊗ t) ⊗ t) ⊗ t))
              ⊖ (Κ (+ 1 / 5040) ⊗
                  ((((((t ⊗ t) ⊗ t) ⊗ t) ⊗ t) ⊗ t) ⊗ t))))
        ⊖ (t ⊗
          (Κ (+ 1 / 1) ⊕
            ((Κ (+ 1 / 1) ⊖ (Κ (+ 1 / 2) ⊗ (t ⊗ t)))
              ⊕ (Κ (+ 1 / 24) ⊗
                  (((t ⊗ t) ⊗ t) ⊗ t))))))
        ⊖ (Κ (+ 1 / 6) ⊗
          ((t ⊗ t) ⊗
            ((t ⊖ (Κ (+ 1 / 6) ⊗ ((t ⊗ t) ⊗ t)))
              ⊕ (Κ (+ 1 / 120) ⊗
                  ((((t ⊗ t) ⊗ t) ⊗ t) ⊗ t)))))
      ⊜ (((((t ⊗ t) ⊗ t) ⊗ t) ⊗ t) ⊗
        (Κ (+ 47 / 20160)
          ⊕ (Κ (+ 1 / 560) ⊗
            (Κ (+ 1 / 4) ⊖ (t ⊗ t))))))
    BishopProperties.≃-refl value

upperCoefficientPolynomialIdentity : ∀ value →
  BishopReal._≃_
    (BishopReal._-_
      (BishopReal._*_
        (embed oneThird)
        (BishopReal._*_
          (square value)
          (BishopReal._-_ value (Low.sineCubicTerm value))))
      (Numerator.inverseDexpNumeratorUpperEnvelope value))
    (BishopReal._*_ (cube value) (upperGapFactor value))
upperCoefficientPolynomialIdentity value =
  let open BishopProperties.ℝ-Solver
  in solve 1
    (λ t →
      ((Κ (+ 1 / 3) ⊗
          ((t ⊗ t) ⊗
            (t ⊖ (Κ (+ 1 / 6) ⊗ ((t ⊗ t) ⊗ t)))))
        ⊖
        ((Κ (+ 2 / 1) ⊗
          ((t ⊖ (Κ (+ 1 / 6) ⊗ ((t ⊗ t) ⊗ t)))
            ⊕ (Κ (+ 1 / 120) ⊗
                ((((t ⊗ t) ⊗ t) ⊗ t) ⊗ t))))
          ⊖ (t ⊗
            (Κ (+ 1 / 1) ⊕
              ((Κ (+ 1 / 1) ⊖ (Κ (+ 1 / 2) ⊗ (t ⊗ t)))
                ⊕ ((Κ (+ 1 / 24) ⊗
                      (((t ⊗ t) ⊗ t) ⊗ t))
                  ⊖ (Κ (+ 1 / 720) ⊗
                      (((((t ⊗ t) ⊗ t) ⊗ t) ⊗ t) ⊗ t)))))))
      ⊜ (((t ⊗ t) ⊗ t) ⊗
        (Κ (+ 1831 / 11520)
          ⊕ ((Κ (+ 11 / 360) ⊗
              (Κ (+ 1 / 4) ⊖ (t ⊗ t)))
            ⊕ (Κ (+ 1 / 720) ⊗
              (Κ (+ 1 / 16) ⊖
                ((t ⊗ t) ⊗ (t ⊗ t))))))))
    BishopProperties.≃-refl value

lowerEnvelopeDominatesOneSixthSquareSineUpper :
  ∀ {dataSet value} →
  Concrete.ConcreteHalfBallSeriesInputs dataSet value →
  BishopReal._≤_
    (BishopReal._*_
      (embed oneSixth)
      (BishopReal._*_
        (square value)
        (Numerator.sineQuinticUpperPolynomial value)))
    (Numerator.inverseDexpNumeratorLowerEnvelope value)
lowerEnvelopeDominatesOneSixthSquareSineUpper {value = value} inputs =
  nonnegativeDifferenceGivesOrder
    (BishopProperties.≤-respʳ-≃
      (BishopProperties.≃-symm
        (lowerCoefficientPolynomialIdentity value))
      (BishopProperties.nonNegx⇒0≤x
        (BishopProperties.nonNegx,y⇒nonNegx*y
          (fifthNonnegative value (Concrete.valueNonnegative inputs))
          (lowerGapFactorNonnegative inputs))))

upperEnvelopeBelowOneThirdSquareSineLower :
  ∀ {dataSet value} →
  Concrete.ConcreteHalfBallSeriesInputs dataSet value →
  BishopReal._≤_
    (Numerator.inverseDexpNumeratorUpperEnvelope value)
    (BishopReal._*_
      (embed oneThird)
      (BishopReal._*_
        (square value)
        (BishopReal._-_ value (Low.sineCubicTerm value))))
upperEnvelopeBelowOneThirdSquareSineLower {value = value} inputs =
  nonnegativeDifferenceGivesOrder
    (BishopProperties.≤-respʳ-≃
      (BishopProperties.≃-symm
        (upperCoefficientPolynomialIdentity value))
      (BishopProperties.nonNegx⇒0≤x
        (BishopProperties.nonNegx,y⇒nonNegx*y
          (cubeNonnegative value (Concrete.valueNonnegative inputs))
          (upperGapFactorNonnegative inputs))))

oneSixthSquareSinBelowNumerator :
  ∀ {dataSet value} →
  Concrete.ConcreteHalfBallSeriesInputs dataSet value →
  BishopReal._≤_
    (BishopReal._*_
      (embed oneSixth)
      (BishopReal._*_
        (square value)
        (Elementary.bishopSin dataSet value)))
    (Numerator.inverseDexpNumerator dataSet value)
oneSixthSquareSinBelowNumerator {dataSet} {value} inputs =
  let
    higher = Higher.higherOrderTaylorBounds inputs
    coefficientTimesSquareNonnegative =
      BishopProperties.nonNegx,y⇒nonNegx*y
        oneSixthNonnegative
        (squareNonnegativeFromInput value
          (Concrete.valueNonnegative inputs))
    sineToUpper = Numerator.multiplyLeftMonotoneNonnegative
      (BishopReal._*_ (embed oneSixth) (square value))
      coefficientTimesSquareNonnegative
      (Higher.sineQuinticUpper higher)
    numeratorBounds = Numerator.inverseDexpNumeratorBounds inputs
  in
  BishopProperties.≤-trans sineToUpper
    (BishopProperties.≤-trans
      (lowerEnvelopeDominatesOneSixthSquareSineUpper inputs)
      (Numerator.lowerEnvelopeBelowNumerator numeratorBounds))

numeratorBelowOneThirdSquareSin :
  ∀ {dataSet value} →
  Concrete.ConcreteHalfBallSeriesInputs dataSet value →
  BishopReal._≤_
    (Numerator.inverseDexpNumerator dataSet value)
    (BishopReal._*_
      (embed oneThird)
      (BishopReal._*_
        (square value)
        (Elementary.bishopSin dataSet value)))
numeratorBelowOneThirdSquareSin {dataSet} {value} inputs =
  let
    low = Low.polynomialTaylorBounds inputs
    coefficientTimesSquareNonnegative =
      BishopProperties.nonNegx,y⇒nonNegx*y
        oneThirdNonnegative
        (squareNonnegativeFromInput value
          (Concrete.valueNonnegative inputs))
    lowerToSine = Numerator.multiplyLeftMonotoneNonnegative
      (BishopReal._*_ (embed oneThird) (square value))
      coefficientTimesSquareNonnegative
      (Low.sineCubicLower low)
    numeratorBounds = Numerator.inverseDexpNumeratorBounds inputs
  in
  BishopProperties.≤-trans
    (Numerator.numeratorBelowUpperEnvelope numeratorBounds)
    (BishopProperties.≤-trans
      (upperEnvelopeBelowOneThirdSquareSineLower inputs)
      lowerToSine)

inverseDexpDenominator :
  Elementary.BishopElementaryPowerSeriesData →
  BishopReal.ℝ → BishopReal.ℝ
inverseDexpDenominator dataSet value =
  BishopReal._*_
    (embed (+ 2 / 1))
    (BishopReal._*_
      (square value)
      (Elementary.bishopSin dataSet value))

record CrossMultipliedInverseDexpCoefficientBounds
    (dataSet : Elementary.BishopElementaryPowerSeriesData)
    (value : BishopReal.ℝ) : Set₁ where
  field
    oneTwelfthDenominatorBelowNumerator :
      BishopReal._≤_
        (BishopReal._*_
          (embed oneTwelfth)
          (inverseDexpDenominator dataSet value))
        (Numerator.inverseDexpNumerator dataSet value)

    numeratorBelowOneSixthDenominator :
      BishopReal._≤_
        (Numerator.inverseDexpNumerator dataSet value)
        (BishopReal._*_
          (embed oneSixth)
          (inverseDexpDenominator dataSet value))

open CrossMultipliedInverseDexpCoefficientBounds public

crossMultipliedInverseDexpCoefficientBounds :
  ∀ {dataSet value} →
  Concrete.ConcreteHalfBallSeriesInputs dataSet value →
  CrossMultipliedInverseDexpCoefficientBounds dataSet value
crossMultipliedInverseDexpCoefficientBounds {dataSet} {value} inputs = record
  { oneTwelfthDenominatorBelowNumerator =
      BishopProperties.≤-respˡ-≃
        (let open BishopProperties.ℝ-Solver
         in solve 1
            (λ denominatorBase →
              Κ (+ 1 / 12) ⊗
                (Κ (+ 2 / 1) ⊗ denominatorBase)
              ⊜ Κ (+ 1 / 6) ⊗ denominatorBase)
            BishopProperties.≃-refl
            (BishopReal._*_
              (square value)
              (Elementary.bishopSin dataSet value)))
        (oneSixthSquareSinBelowNumerator inputs)
  ; numeratorBelowOneSixthDenominator =
      BishopProperties.≤-respʳ-≃
        (let open BishopProperties.ℝ-Solver
         in solve 1
            (λ denominatorBase →
              Κ (+ 1 / 3) ⊗ denominatorBase
              ⊜ Κ (+ 1 / 6) ⊗
                (Κ (+ 2 / 1) ⊗ denominatorBase))
            BishopProperties.≃-refl
            (BishopReal._*_
              (square value)
              (Elementary.bishopSin dataSet value)))
        (numeratorBelowOneThirdSquareSin inputs)
  }

p33InverseDexpCrossMultipliedCoefficientLevel : ProofLevel
p33InverseDexpCrossMultipliedCoefficientLevel = machineChecked
