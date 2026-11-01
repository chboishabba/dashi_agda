module DASHI.Physics.YangMills.BalabanP33BishopInverseDexpActualEndpointModulusExact where

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
-- Upgrade the rational seventh-order endpoint check to the actual Bishop sine
-- and cosine.  Put
--
--   n(t) = 2 sin t - t(1+cos t),
--   d(t) = 2 t^2 sin t,
--   E(t) = n(t) - d(t)/12.
--
-- The alternating Taylor brackets give
--
--   E(t) <= t^5 (1/360 + t^4/30240).
--
-- On t^2 <= 1/4 the parenthesis is at most 269/96768, while
-- sin t >= (23/24)t gives
--
--   (t^2/100)d(t) >= (23/1200)t^5.
--
-- Since 269/96768 < 23/1200, this proves on the entire nonnegative
-- constructive half-ball
--
--   0 <= E(t) <= (t^2/100)d(t).
------------------------------------------------------------------------

open import Data.Integer.Base using (+_; nonNeg)
open import Data.Rational.Unnormalised as ℚ using (ℚᵘ; 0ℚᵘ; _/_)
import Data.Rational.Unnormalised.Properties as ℚP

import Real as BishopReal
import RealProperties as BishopProperties

import DASHI.Foundations.BishopPowerSeriesElementaryBridgeExact as Elementary
import DASHI.Physics.YangMills.BalabanBishopConcreteSineCosineInterlacingExact as Concrete
import DASHI.Physics.YangMills.BalabanP33BishopTaylorPolynomialFormExact as Low
import DASHI.Physics.YangMills.BalabanP33BishopHigherOrderTaylorExact as Higher
import DASHI.Physics.YangMills.BalabanP33BishopInverseDexpNumeratorExact as Numerator
import DASHI.Physics.YangMills.BalabanP33BishopInverseDexpCoefficientExact as Cross
import DASHI.Physics.YangMills.BalabanP33BishopInverseDexpPositiveDenominatorExact as Positive
open import DASHI.Physics.YangMills.CompactLieProofLevel

oneTwelfth oneSixth oneHundred oneFiftieth : ℚᵘ
oneTwelfth = + 1 / 12
oneSixth = + 1 / 6
oneHundred = + 1 / 100
oneFiftieth = + 1 / 50

oneThreeSixtieth oneThirtyThousandTwoFortieth : ℚᵘ
oneThreeSixtieth = + 1 / 360
oneThirtyThousandTwoFortieth = + 1 / 30240

oneSixteenth twentyThreeTwentyFourth twentyThreeTwelveHundred : ℚᵘ
oneSixteenth = + 1 / 16
twentyThreeTwentyFourth = + 23 / 24
twentyThreeTwelveHundred = + 23 / 1200

factorCeiling factorGap : ℚᵘ
factorCeiling = + 269 / 96768
factorGap = + 39643 / 2419200

embed : ℚᵘ → BishopReal.ℝ
embed = BishopReal._⋆

square fourth fifth : BishopReal.ℝ → BishopReal.ℝ
square value = BishopReal._*_ value value
fourth value = BishopReal._*_ (square value) (square value)
fifth value = BishopReal._*_ (fourth value) value

actualEndpointDefect :
  Elementary.BishopElementaryPowerSeriesData →
  BishopReal.ℝ → BishopReal.ℝ
actualEndpointDefect dataSet value =
  BishopReal._-_
    (Numerator.inverseDexpNumerator dataSet value)
    (BishopReal._*_
      (embed oneTwelfth)
      (Cross.inverseDexpDenominator dataSet value))

upperTaylorFactor : BishopReal.ℝ → BishopReal.ℝ
upperTaylorFactor value =
  BishopReal._+_
    (embed oneThreeSixtieth)
    (BishopReal._*_
      (embed oneThirtyThousandTwoFortieth)
      (fourth value))

upperTaylorDefect : BishopReal.ℝ → BishopReal.ℝ
upperTaylorDefect value =
  BishopReal._*_ (fifth value) (upperTaylorFactor value)

oneSixthSquare : BishopReal.ℝ → BishopReal.ℝ
oneSixthSquare value =
  BishopReal._*_ (embed oneSixth) (square value)

oneTwelfthDenominatorIsOneSixthSquareSine :
  ∀ dataSet value →
  BishopReal._≃_
    (BishopReal._*_
      (embed oneTwelfth)
      (Cross.inverseDexpDenominator dataSet value))
    (BishopReal._*_
      (oneSixthSquare value)
      (Elementary.bishopSin dataSet value))
oneTwelfthDenominatorIsOneSixthSquareSine dataSet value =
  let open BishopProperties.ℝ-Solver
  in solve 2
    (λ t sineValue →
      Κ (+ 1 / 12) ⊗
        (Κ (+ 2 / 1) ⊗ ((t ⊗ t) ⊗ sineValue))
      ⊜ (Κ (+ 1 / 6) ⊗ (t ⊗ t)) ⊗ sineValue)
    BishopProperties.≃-refl value
    (Elementary.bishopSin dataSet value)

upperEnvelopeMinusLowerSineIdentity : ∀ value →
  BishopReal._≃_
    (BishopReal._-_
      (Numerator.inverseDexpNumeratorUpperEnvelope value)
      (BishopReal._*_
        (oneSixthSquare value)
        (Numerator.sineSepticLowerPolynomial value)))
    (upperTaylorDefect value)
upperEnvelopeMinusLowerSineIdentity value =
  let open BishopProperties.ℝ-Solver
  in solve 1
    (λ t →
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
                    (((((t ⊗ t) ⊗ t) ⊗ t) ⊗ t) ⊗ t))))))
        ⊖ ((Κ (+ 1 / 6) ⊗ (t ⊗ t)) ⊗
          ((t ⊖ (Κ (+ 1 / 6) ⊗ ((t ⊗ t) ⊗ t)))
            ⊕ ((Κ (+ 1 / 120) ⊗
                  ((((t ⊗ t) ⊗ t) ⊗ t) ⊗ t))
              ⊖ (Κ (+ 1 / 5040) ⊗
                  ((((((t ⊗ t) ⊗ t) ⊗ t) ⊗ t) ⊗ t) ⊗ t))))))
      ⊜ (((((t ⊗ t) ⊗ t) ⊗ t) ⊗ t) ⊗
        (Κ (+ 1 / 360)
          ⊕ (Κ (+ 1 / 30240) ⊗
            ((t ⊗ t) ⊗ (t ⊗ t))))))
    BishopProperties.≃-refl value

oneSixthSquareNonnegative : ∀ {dataSet value} →
  Concrete.ConcreteHalfBallSeriesInputs dataSet value →
  BishopReal.NonNegative (oneSixthSquare value)
oneSixthSquareNonnegative {value = value} inputs =
  BishopProperties.nonNegx,y⇒nonNegx*y
    Cross.oneSixthNonnegative
    (Cross.squareNonnegativeFromInput value
      (Concrete.valueNonnegative inputs))

actualDefectBelowTaylorDefect :
  ∀ {dataSet value} →
  Concrete.ConcreteHalfBallSeriesInputs dataSet value →
  BishopReal._≤_
    (actualEndpointDefect dataSet value)
    (upperTaylorDefect value)
actualDefectBelowTaylorDefect {dataSet} {value} inputs =
  let
    numeratorBounds = Numerator.inverseDexpNumeratorBounds inputs
    higherBounds = Higher.higherOrderTaylorBounds inputs
    lowerSineScaled =
      Numerator.multiplyLeftMonotoneNonnegative
        (oneSixthSquare value)
        (oneSixthSquareNonnegative inputs)
        (Higher.sineSepticLower higherBounds)
    lowerSineBelowDenominator :
      BishopReal._≤_
        (BishopReal._*_
          (oneSixthSquare value)
          (Numerator.sineSepticLowerPolynomial value))
        (BishopReal._*_
          (embed oneTwelfth)
          (Cross.inverseDexpDenominator dataSet value))
    lowerSineBelowDenominator =
      BishopProperties.≤-respʳ-≃
        (BishopProperties.≃-symm
          (oneTwelfthDenominatorIsOneSixthSquareSine dataSet value))
        lowerSineScaled
    rawUpper =
      BishopProperties.+-mono-≤
        (Numerator.numeratorBelowUpperEnvelope numeratorBounds)
        (BishopProperties.neg-mono-≤ lowerSineBelowDenominator)
    leftMeaning :
      BishopReal._≃_
        (actualEndpointDefect dataSet value)
        (BishopReal._+_
          (Numerator.inverseDexpNumerator dataSet value)
          (BishopReal.-
            (BishopReal._*_
              (embed oneTwelfth)
              (Cross.inverseDexpDenominator dataSet value))))
    leftMeaning = BishopProperties.≃-refl
  in
  BishopProperties.≤-respʳ-≃
    (upperEnvelopeMinusLowerSineIdentity value)
    (BishopProperties.≤-respˡ-≃
      (BishopProperties.≃-symm leftMeaning)
      rawUpper)

upperFactorAtSixteenth : BishopReal.ℝ
upperFactorAtSixteenth =
  BishopReal._+_
    (embed oneThreeSixtieth)
    (BishopReal._*_
      (embed oneThirtyThousandTwoFortieth)
      (embed oneSixteenth))

upperFactorAtSixteenthIsCeiling :
  BishopReal._≃_ upperFactorAtSixteenth (embed factorCeiling)
upperFactorAtSixteenthIsCeiling =
  let open BishopProperties.ℝ-Solver
  in solve 0
    ((Κ (+ 1 / 360)
      ⊕ (Κ (+ 1 / 30240) ⊗ Κ (+ 1 / 16)))
      ⊜ Κ (+ 269 / 96768))
    BishopProperties.≃-refl

upperTaylorFactorBelowCeiling :
  ∀ {dataSet value} →
  Concrete.ConcreteHalfBallSeriesInputs dataSet value →
  BishopReal._≤_ (upperTaylorFactor value) (embed factorCeiling)
upperTaylorFactorBelowCeiling {value = value} inputs =
  let
    scaledFourth =
      BishopProperties.*-monoˡ-≤-nonNeg
        (Cross.fourthBelowSixteenth inputs)
        (Cross.embeddedRationalNonnegative
          oneThirtyThousandTwoFortieth nonNeg)
    added = BishopProperties.+-monoʳ-≤
      (embed oneThreeSixtieth) scaledFourth
  in
  BishopProperties.≤-respʳ-≃
    upperFactorAtSixteenthIsCeiling added

upperTaylorDefectBelowCeilingFifth :
  ∀ {dataSet value} →
  Concrete.ConcreteHalfBallSeriesInputs dataSet value →
  BishopReal._≤_
    (upperTaylorDefect value)
    (BishopReal._*_ (fifth value) (embed factorCeiling))
upperTaylorDefectBelowCeilingFifth {value = value} inputs =
  BishopProperties.*-monoˡ-≤-nonNeg
    (upperTaylorFactorBelowCeiling inputs)
    (Cross.fifthNonnegative value (Concrete.valueNonnegative inputs))

factorGapIdentity :
  BishopReal._≃_
    (BishopReal._-_
      (embed twentyThreeTwelveHundred)
      (embed factorCeiling))
    (embed factorGap)
factorGapIdentity =
  let open BishopProperties.ℝ-Solver
  in solve 0
    ((Κ (+ 23 / 1200) ⊖ Κ (+ 269 / 96768))
      ⊜ Κ (+ 39643 / 2419200))
    BishopProperties.≃-refl

factorCeilingBelowTwentyThreeTwelveHundred :
  BishopReal._≤_
    (embed factorCeiling)
    (embed twentyThreeTwelveHundred)
factorCeilingBelowTwentyThreeTwelveHundred =
  Cross.nonnegativeDifferenceGivesOrder
    (BishopProperties.≤-respʳ-≃
      (BishopProperties.≃-symm factorGapIdentity)
      (BishopProperties.nonNegx⇒0≤x
        (Cross.embeddedRationalNonnegative factorGap nonNeg)))

ceilingFifthBelowCoarseFifth :
  ∀ {dataSet value} →
  Concrete.ConcreteHalfBallSeriesInputs dataSet value →
  BishopReal._≤_
    (BishopReal._*_ (fifth value) (embed factorCeiling))
    (BishopReal._*_
      (fifth value) (embed twentyThreeTwelveHundred))
ceilingFifthBelowCoarseFifth {value = value} inputs =
  BishopProperties.*-monoˡ-≤-nonNeg
    factorCeilingBelowTwentyThreeTwelveHundred
    (Cross.fifthNonnegative value (Concrete.valueNonnegative inputs))

coarseSineLower :
  ∀ {dataSet value} →
  Concrete.ConcreteHalfBallSeriesInputs dataSet value →
  BishopReal._≤_
    (BishopReal._*_ (embed twentyThreeTwentyFourth) value)
    (Elementary.bishopSin dataSet value)
coarseSineLower {dataSet} {value} inputs =
  let
    valueNonnegative = Concrete.valueNonnegative inputs
    scaledFactor =
      BishopProperties.*-monoˡ-≤-nonNeg
        (Positive.oneMinusSixthSquareAboveTwentyThreeTwentyFourth inputs)
        valueNonnegative
    scaledMeaning :
      BishopReal._≃_
        (BishopReal._*_ value (embed twentyThreeTwentyFourth))
        (BishopReal._*_ (embed twentyThreeTwentyFourth) value)
    scaledMeaning = BishopProperties.*-comm
      value (embed twentyThreeTwentyFourth)
    lowerToCubic =
      BishopProperties.≤-respˡ-≃ scaledMeaning
        (BishopProperties.≤-respʳ-≃
          (BishopProperties.≃-symm
            (Positive.cubicSineLowerFactors value))
          scaledFactor)
  in
  BishopProperties.≤-trans
    lowerToCubic
    (Low.sineCubicLower (Low.polynomialTaylorBounds inputs))

quadraticDenominatorScale :
  Elementary.BishopElementaryPowerSeriesData →
  BishopReal.ℝ → BishopReal.ℝ
quadraticDenominatorScale dataSet value =
  BishopReal._*_
    (BishopReal._*_
      (embed oneHundred) (square value))
    (Cross.inverseDexpDenominator dataSet value)

coarseLowerScaledIdentity : ∀ value →
  BishopReal._≃_
    (BishopReal._*_
      (BishopReal._*_
        (embed oneFiftieth) (fourth value))
      (BishopReal._*_
        (embed twentyThreeTwentyFourth) value))
    (BishopReal._*_
      (fifth value) (embed twentyThreeTwelveHundred))
coarseLowerScaledIdentity value =
  let open BishopProperties.ℝ-Solver
  in solve 1
    (λ t →
      ((Κ (+ 1 / 50) ⊗
          ((t ⊗ t) ⊗ (t ⊗ t)))
        ⊗ (Κ (+ 23 / 24) ⊗ t))
      ⊜ (((((t ⊗ t) ⊗ t) ⊗ t) ⊗ t)
        ⊗ Κ (+ 23 / 1200)))
    BishopProperties.≃-refl value

quadraticDenominatorScaleIdentity : ∀ dataSet value →
  BishopReal._≃_
    (quadraticDenominatorScale dataSet value)
    (BishopReal._*_
      (BishopReal._*_
        (embed oneFiftieth) (fourth value))
      (Elementary.bishopSin dataSet value))
quadraticDenominatorScaleIdentity dataSet value =
  let open BishopProperties.ℝ-Solver
  in solve 2
    (λ t sineValue →
      ((Κ (+ 1 / 100) ⊗ (t ⊗ t))
        ⊗ (Κ (+ 2 / 1) ⊗ ((t ⊗ t) ⊗ sineValue)))
      ⊜ ((Κ (+ 1 / 50) ⊗
          ((t ⊗ t) ⊗ (t ⊗ t)))
        ⊗ sineValue))
    BishopProperties.≃-refl value
    (Elementary.bishopSin dataSet value)

coarseFifthBelowQuadraticDenominator :
  ∀ {dataSet value} →
  Concrete.ConcreteHalfBallSeriesInputs dataSet value →
  BishopReal._≤_
    (BishopReal._*_
      (fifth value) (embed twentyThreeTwelveHundred))
    (quadraticDenominatorScale dataSet value)
coarseFifthBelowQuadraticDenominator {dataSet} {value} inputs =
  let
    multiplier =
      BishopReal._*_
        (embed oneFiftieth) (fourth value)
    multiplierNonnegative =
      BishopProperties.nonNegx,y⇒nonNegx*y
        (Cross.embeddedRationalNonnegative oneFiftieth nonNeg)
        (Cross.fourthNonnegative value
          (Concrete.valueNonnegative inputs))
    scaledSine =
      Numerator.multiplyLeftMonotoneNonnegative
        multiplier multiplierNonnegative (coarseSineLower inputs)
  in
  BishopProperties.≤-respʳ-≃
    (BishopProperties.≃-symm
      (quadraticDenominatorScaleIdentity dataSet value))
    (BishopProperties.≤-respˡ-≃
      (coarseLowerScaledIdentity value)
      scaledSine)

actualEndpointDefectNonnegative :
  ∀ {dataSet value} →
  Concrete.ConcreteHalfBallSeriesInputs dataSet value →
  BishopReal._≤_
    BishopReal.0ℝ
    (actualEndpointDefect dataSet value)
actualEndpointDefectNonnegative inputs =
  Low.orderGivesNonnegativeDifference
    (Cross.oneTwelfthDenominatorBelowNumerator
      (Cross.crossMultipliedInverseDexpCoefficientBounds inputs))

actualEndpointDefectQuadraticModulus :
  ∀ {dataSet value} →
  Concrete.ConcreteHalfBallSeriesInputs dataSet value →
  BishopReal._≤_
    (actualEndpointDefect dataSet value)
    (quadraticDenominatorScale dataSet value)
actualEndpointDefectQuadraticModulus inputs =
  BishopProperties.≤-trans
    (actualDefectBelowTaylorDefect inputs)
    (BishopProperties.≤-trans
      (upperTaylorDefectBelowCeilingFifth inputs)
      (BishopProperties.≤-trans
        (ceilingFifthBelowCoarseFifth inputs)
        (coarseFifthBelowQuadraticDenominator inputs)))

p33ActualEndpointTaylorRemainderLevel : ProofLevel
p33ActualEndpointTaylorRemainderLevel = machineChecked

p33ActualEndpointNonnegativeLevel : ProofLevel
p33ActualEndpointNonnegativeLevel = machineChecked

p33ActualEndpointQuadraticModulusLevel : ProofLevel
p33ActualEndpointQuadraticModulusLevel = machineChecked
