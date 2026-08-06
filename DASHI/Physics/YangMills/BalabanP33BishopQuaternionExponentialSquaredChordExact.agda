module DASHI.Physics.YangMills.BalabanP33BishopQuaternionExponentialSquaredChordExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Brian C. Hall,
-- "Lie Groups, Lie Algebras, and Representations: An Elementary
-- Introduction", second edition, Springer, 2015.
-- DOI: 10.1007/978-3-319-13467-3.
--
-- Zachary Murray,
-- "Constructive Analysis in the Agda Proof Assistant",
-- B.Sc. Honours thesis, Dalhousie University, 2022.
-- arXiv:2205.08354. No DOI assigned.
--
-- The formula agrees with the pure-imaginary quaternion exponential used in
-- the reviewed mathlib quaternion development (`Quaternion.exp_of_re_eq_zero`).
-- DASHI does not import Lean evidence; the proof below is internal to the
-- Bishop-real sine/cosine series and their checked alternating bounds.
--
-- DASHI CONTRIBUTION
--
-- For the literal constructive sine and cosine, define the radial squared
-- chord from exp(X) to 1 by
--
--   Delta(t) = (1-cos t)^2 + sin^2 t.
--
-- Instead of postulating sin^2+cos^2=1, prove directly from the already checked
-- half-ball Taylor brackets that
--
--   Delta(t) <= t^2,          0 <= t, |t| <= 1/2.
--
-- This is the square-root-free content of
--
--   d_ch(exp X,1) <= ||X||.
--
-- The decisive polynomial gap is
--
--   t^2 - [(t-t^3/6+t^5/120)^2 + (t^2/2)^2]
--     = t^4/14400 (1200 - 640u + 40u^2 - u^3),  u=t^2,
--
-- and on u<=1/4 the final factor is exhibited as a sum of nonnegative terms:
--
--   1200 - 640u + 40u^2 - u^3
--     = 66559/64
--       + (10241/16)(1/4-u)
--       + 40u^2
--       + u(1/16-u^2).
--
-- Thus this theorem does not depend on an unimplemented Pythagorean authority.
-- A later square-root construction need only transport this checked squared
-- order through monotonicity; it does not carry further trigonometric risk.
------------------------------------------------------------------------

open import Data.Integer.Base using (+_; nonNeg)
open import Data.Rational.Unnormalised as ℚ using (ℚᵘ; _/_)

import Real as BishopReal
import RealProperties as BishopProperties

import DASHI.Foundations.BishopPowerSeriesElementaryBridgeExact as Elementary
import DASHI.Physics.YangMills.BalabanBishopConcreteSineCosineInterlacingExact as Concrete
import DASHI.Physics.YangMills.BalabanP33BishopTaylorPolynomialFormExact as Low
import DASHI.Physics.YangMills.BalabanP33BishopHigherOrderTaylorExact as Higher
import DASHI.Physics.YangMills.BalabanP33BishopInverseDexpNumeratorExact as Numerator
import DASHI.Physics.YangMills.BalabanP33BishopInverseDexpCoefficientExact as Cross
import DASHI.Physics.YangMills.BalabanP33BishopInverseDexpActualEndpointModulusExact as Endpoint
open import DASHI.Physics.YangMills.CompactLieProofLevel

oneHalf oneQuarter oneSixteenth oneFourteenFourHundred : ℚᵘ
oneHalf = + 1 / 2
oneQuarter = + 1 / 4
oneSixteenth = + 1 / 16
oneFourteenFourHundred = + 1 / 14400

twentyThreeTwentyFourth forty : ℚᵘ
twentyThreeTwentyFourth = + 23 / 24
forty = + 40 / 1

positiveCore gapCoefficient : ℚᵘ
positiveCore = + 66559 / 64
gapCoefficient = + 10241 / 16

embed : ℚᵘ → BishopReal.ℝ
embed = BishopReal._⋆

square fourth : BishopReal.ℝ → BishopReal.ℝ
square value = BishopReal._*_ value value
fourth value = BishopReal._*_ (square value) (square value)

cosineDefect :
  Elementary.BishopElementaryPowerSeriesData →
  BishopReal.ℝ → BishopReal.ℝ
cosineDefect dataSet value =
  BishopReal._-_ BishopReal.1ℝ (Elementary.bishopCos dataSet value)

actualSquaredChord :
  Elementary.BishopElementaryPowerSeriesData →
  BishopReal.ℝ → BishopReal.ℝ
actualSquaredChord dataSet value =
  BishopReal._+_
    (square (cosineDefect dataSet value))
    (square (Elementary.bishopSin dataSet value))

sineUpperPolynomial : BishopReal.ℝ → BishopReal.ℝ
sineUpperPolynomial = Numerator.sineQuinticUpperPolynomial

cosineDefectUpperPolynomial : BishopReal.ℝ → BishopReal.ℝ
cosineDefectUpperPolynomial value =
  BishopReal._*_ (embed oneHalf) (square value)

polynomialChordMajorant : BishopReal.ℝ → BishopReal.ℝ
polynomialChordMajorant value =
  BishopReal._+_
    (square (cosineDefectUpperPolynomial value))
    (square (sineUpperPolynomial value))

squareMonotoneNonnegative :
  ∀ {left right} →
  BishopReal.NonNegative left →
  BishopReal._≤_ left right →
  BishopReal._≤_ (square left) (square right)
squareMonotoneNonnegative {left} {right} leftNonnegative leftBelowRight =
  BishopProperties.*-mono-≤
    leftNonnegative leftNonnegative leftBelowRight leftBelowRight

embeddedTwentyThreeTwentyFourthNonnegative :
  BishopReal.NonNegative (embed twentyThreeTwentyFourth)
embeddedTwentyThreeTwentyFourthNonnegative =
  Cross.embeddedRationalNonnegative twentyThreeTwentyFourth nonNeg

coarseSineLowerNonnegative :
  ∀ {dataSet value} →
  Concrete.ConcreteHalfBallSeriesInputs dataSet value →
  BishopReal.NonNegative
    (BishopReal._*_ (embed twentyThreeTwentyFourth) value)
coarseSineLowerNonnegative inputs =
  BishopProperties.nonNegx,y⇒nonNegx*y
    embeddedTwentyThreeTwentyFourthNonnegative
    (Concrete.valueNonnegative inputs)

actualSineNonnegative :
  ∀ {dataSet value} →
  Concrete.ConcreteHalfBallSeriesInputs dataSet value →
  BishopReal.NonNegative (Elementary.bishopSin dataSet value)
actualSineNonnegative inputs =
  BishopProperties.0≤x⇒nonNegx
    (BishopProperties.≤-trans
      (BishopProperties.nonNegx⇒0≤x
        (coarseSineLowerNonnegative inputs))
      (Endpoint.coarseSineLower inputs))

sineUpperPolynomialNonnegative :
  ∀ {dataSet value} →
  Concrete.ConcreteHalfBallSeriesInputs dataSet value →
  BishopReal.NonNegative (sineUpperPolynomial value)
sineUpperPolynomialNonnegative inputs =
  BishopProperties.0≤x⇒nonNegx
    (BishopProperties.≤-trans
      (BishopProperties.nonNegx⇒0≤x (actualSineNonnegative inputs))
      (Higher.sineQuinticUpper (Higher.higherOrderTaylorBounds inputs)))

cosineDefectUpperNonnegative :
  ∀ {dataSet value} →
  Concrete.ConcreteHalfBallSeriesInputs dataSet value →
  BishopReal.NonNegative (cosineDefectUpperPolynomial value)
cosineDefectUpperNonnegative {value = value} inputs =
  BishopProperties.nonNegx,y⇒nonNegx*y
    (Cross.embeddedRationalNonnegative oneHalf nonNeg)
    (Cross.squareNonnegativeFromInput value
      (Concrete.valueNonnegative inputs))

actualChordBelowPolynomialChord :
  ∀ {dataSet value} →
  Concrete.ConcreteHalfBallSeriesInputs dataSet value →
  BishopReal._≤_
    (actualSquaredChord dataSet value)
    (polynomialChordMajorant value)
actualChordBelowPolynomialChord {dataSet} {value} inputs =
  let
    lowBounds = Low.defectTaylorBounds inputs
    highBounds = Higher.higherOrderTaylorBounds inputs
    cosineSquareBound =
      squareMonotoneNonnegative
        (BishopProperties.0≤x⇒nonNegx
          (Low.cosineDefectNonnegative lowBounds))
        (Low.cosineDefectBelowQuadratic lowBounds)
    sineSquareBound =
      squareMonotoneNonnegative
        (actualSineNonnegative inputs)
        (Higher.sineQuinticUpper highBounds)
  in
  BishopProperties.+-mono-≤ cosineSquareBound sineSquareBound

squareGap : BishopReal.ℝ → BishopReal.ℝ
squareGap value =
  BishopReal._-_ (embed oneQuarter) (square value)

fourthGap : BishopReal.ℝ → BishopReal.ℝ
fourthGap value =
  BishopReal._-_ (embed oneSixteenth) (fourth value)

polynomialGapFactor : BishopReal.ℝ → BishopReal.ℝ
polynomialGapFactor value =
  BishopReal._+_
    (embed positiveCore)
    (BishopReal._+_
      (BishopReal._*_ (embed gapCoefficient) (squareGap value))
      (BishopReal._+_
        (BishopReal._*_ (embed forty) (fourth value))
        (BishopReal._*_ (square value) (fourthGap value))))

polynomialGapFactorNonnegative :
  ∀ {dataSet value} →
  Concrete.ConcreteHalfBallSeriesInputs dataSet value →
  BishopReal.NonNegative (polynomialGapFactor value)
polynomialGapFactorNonnegative {value = value} inputs =
  BishopProperties.nonNegx,y⇒nonNegx+y
    (Cross.embeddedRationalNonnegative positiveCore nonNeg)
    (BishopProperties.nonNegx,y⇒nonNegx+y
      (BishopProperties.nonNegx,y⇒nonNegx*y
        (Cross.embeddedRationalNonnegative gapCoefficient nonNeg)
        (Cross.squareGapNonnegative inputs))
      (BishopProperties.nonNegx,y⇒nonNegx+y
        (BishopProperties.nonNegx,y⇒nonNegx*y
          (Cross.embeddedRationalNonnegative forty nonNeg)
          (Cross.fourthNonnegative value
            (Concrete.valueNonnegative inputs)))
        (BishopProperties.nonNegx,y⇒nonNegx*y
          (Cross.squareNonnegativeFromInput value
            (Concrete.valueNonnegative inputs))
          (Cross.fourthGapNonnegative inputs))))

polynomialChordGapIdentity : ∀ value →
  BishopReal._≃_
    (BishopReal._-_ (square value) (polynomialChordMajorant value))
    (BishopReal._*_
      (BishopReal._*_
        (embed oneFourteenFourHundred)
        (fourth value))
      (polynomialGapFactor value))
polynomialChordGapIdentity value =
  let open BishopProperties.ℝ-Solver
  in solve 1
    (λ t →
      ((t ⊗ t)
        ⊖ (((Κ (+ 1 / 2) ⊗ (t ⊗ t))
              ⊗ (Κ (+ 1 / 2) ⊗ (t ⊗ t)))
          ⊕ ((t
                ⊖ (Κ (+ 1 / 6) ⊗ ((t ⊗ t) ⊗ t))
                ⊕ (Κ (+ 1 / 120) ⊗
                  ((((t ⊗ t) ⊗ t) ⊗ t) ⊗ t)))
              ⊗ (t
                ⊖ (Κ (+ 1 / 6) ⊗ ((t ⊗ t) ⊗ t))
                ⊕ (Κ (+ 1 / 120) ⊗
                  ((((t ⊗ t) ⊗ t) ⊗ t) ⊗ t)))))
      ⊜ ((Κ (+ 1 / 14400) ⊗
            ((t ⊗ t) ⊗ (t ⊗ t)))
          ⊗
          (Κ (+ 66559 / 64)
            ⊕ ((Κ (+ 10241 / 16)
                  ⊗ (Κ (+ 1 / 4) ⊖ (t ⊗ t)))
              ⊕ ((Κ (+ 40 / 1)
                    ⊗ ((t ⊗ t) ⊗ (t ⊗ t)))
                ⊕ ((t ⊗ t)
                    ⊗ (Κ (+ 1 / 16)
                      ⊖ ((t ⊗ t) ⊗ (t ⊗ t))))))))))
    BishopProperties.≃-refl value

polynomialChordMajorantBelowRadiusSquared :
  ∀ {dataSet value} →
  Concrete.ConcreteHalfBallSeriesInputs dataSet value →
  BishopReal._≤_ (polynomialChordMajorant value) (square value)
polynomialChordMajorantBelowRadiusSquared {value = value} inputs =
  Cross.nonnegativeDifferenceGivesOrder
    (BishopProperties.≤-respʳ-≃
      (BishopProperties.≃-symm (polynomialChordGapIdentity value))
      (BishopProperties.nonNegx⇒0≤x
        (BishopProperties.nonNegx,y⇒nonNegx*y
          (BishopProperties.nonNegx,y⇒nonNegx*y
            (Cross.embeddedRationalNonnegative oneFourteenFourHundred nonNeg)
            (Cross.fourthNonnegative value
              (Concrete.valueNonnegative inputs)))
          (polynomialGapFactorNonnegative inputs))))

actualSquaredChordBelowRadiusSquared :
  ∀ {dataSet value} →
  Concrete.ConcreteHalfBallSeriesInputs dataSet value →
  BishopReal._≤_
    (actualSquaredChord dataSet value)
    (square value)
actualSquaredChordBelowRadiusSquared inputs =
  BishopProperties.≤-trans
    (actualChordBelowPolynomialChord inputs)
    (polynomialChordMajorantBelowRadiusSquared inputs)

------------------------------------------------------------------------
-- Exact 2-2cos identity, isolated from its scalar Pythagorean input.
-- This is useful for a backend that later proves sin^2+cos^2=1 by Cauchy
-- products; the inequality above does not wait for that theorem.
------------------------------------------------------------------------

record BishopPythagoreanAt
    (dataSet : Elementary.BishopElementaryPowerSeriesData)
    (value : BishopReal.ℝ) : Set where
  field
    pythagorean :
      BishopReal._≃_
        (BishopReal._+_
          (square (Elementary.bishopCos dataSet value))
          (square (Elementary.bishopSin dataSet value)))
        BishopReal.1ℝ

open BishopPythagoreanAt public

twoMinusTwoCosine :
  Elementary.BishopElementaryPowerSeriesData →
  BishopReal.ℝ → BishopReal.ℝ
twoMinusTwoCosine dataSet value =
  BishopReal._-_
    (embed (+ 2 / 1))
    (BishopReal._*_
      (embed (+ 2 / 1))
      (Elementary.bishopCos dataSet value))

actualSquaredChordIsTwoMinusTwoCosine :
  ∀ {dataSet value} →
  BishopPythagoreanAt dataSet value →
  BishopReal._≃_
    (actualSquaredChord dataSet value)
    (twoMinusTwoCosine dataSet value)
actualSquaredChordIsTwoMinusTwoCosine {dataSet} {value} pythagoreanData =
  let open BishopProperties.ℝ-Solver
      sineValue = Elementary.bishopSin dataSet value
      cosineValue = Elementary.bishopCos dataSet value
      normalized :
        BishopReal._≃_
          (BishopReal._+_ (square cosineValue) (square sineValue))
          BishopReal.1ℝ
      normalized = pythagorean pythagoreanData
  in
  BishopProperties.≃-trans
    (solve 2
      (λ c s →
        (((Κ (+ 1 / 1) ⊖ c) ⊗ (Κ (+ 1 / 1) ⊖ c))
          ⊕ (s ⊗ s))
        ⊜ ((c ⊗ c ⊕ s ⊗ s)
          ⊕ (Κ (+ 1 / 1) ⊖ (Κ (+ 2 / 1) ⊗ c))))
      BishopProperties.≃-refl cosineValue sineValue)
    (BishopProperties.≃-trans
      (BishopProperties.+-cong normalized BishopProperties.≃-refl)
      (solve 1
        (λ c →
          Κ (+ 1 / 1)
            ⊕ (Κ (+ 1 / 1) ⊖ (Κ (+ 2 / 1) ⊗ c))
          ⊜ Κ (+ 2 / 1) ⊖ (Κ (+ 2 / 1) ⊗ c))
        BishopProperties.≃-refl cosineValue))

p33ActualBishopSquaredChordBoundLevel : ProofLevel
p33ActualBishopSquaredChordBoundLevel = machineChecked

p33ChordPythagoreanReductionLevel : ProofLevel
p33ChordPythagoreanReductionLevel = machineChecked

bishopPythagoreanCauchyProductInputLevel : ProofLevel
bishopPythagoreanCauchyProductInputLevel = conditional
