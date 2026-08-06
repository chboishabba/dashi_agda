module DASHI.Physics.YangMills.BalabanP33BishopInverseDexpPositiveDenominatorExact where

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
-- Put
--
--   n(t) = 2 sin t - t(1 + cos t),
--   d(t) = 2 t^2 sin t.
--
-- The previous P33 theorem proved
--
--   (1/12)d(t) <= n(t) <= (1/6)d(t)
--
-- without division.  This module proves constructively that d(t)>0 on the
-- strictly positive half ball.  Indeed,
--
--   sin t >= t(1-t^2/6) >= (23/24)t > 0.
--
-- The Bishop inverse of d(t) therefore exists and is positive, so the literal
-- quotient beta(t)=n(t)d(t)^-1 satisfies 1/12 <= beta(t) <= 1/6.  The t=0
-- branch is defined separately as 1/12; no equality decision or trichotomy on
-- constructive reals is assumed.
------------------------------------------------------------------------

open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised as ℚ using (ℚᵘ; 0ℚᵘ; _/_)
import Data.Rational.Unnormalised.Properties as ℚP
open import Data.Sum.Base using (inj₂)

import Real as BishopReal
import RealProperties as BishopProperties
import Inverse as BishopInverse

import DASHI.Foundations.BishopPowerSeriesElementaryBridgeExact as Elementary
import DASHI.Physics.YangMills.BalabanBishopConcreteSineCosineInterlacingExact as Concrete
import DASHI.Physics.YangMills.BalabanP33BishopTaylorPolynomialFormExact as Low
import DASHI.Physics.YangMills.BalabanP33BishopInverseDexpNumeratorExact as Numerator
import DASHI.Physics.YangMills.BalabanP33BishopInverseDexpCoefficientExact as Cross
open import DASHI.Physics.YangMills.CompactLieProofLevel

oneTwelfth oneSixth twentyThreeTwentyFourth two : ℚᵘ
oneTwelfth = + 1 / 12
oneSixth = + 1 / 6
twentyThreeTwentyFourth = + 23 / 24
two = + 2 / 1

embed : ℚᵘ → BishopReal.ℝ
embed = BishopReal._⋆

square : BishopReal.ℝ → BishopReal.ℝ
square value = BishopReal._*_ value value

positiveTwentyThreeTwentyFourth :
  BishopReal._<_ BishopReal.0ℝ (embed twentyThreeTwentyFourth)
positiveTwentyThreeTwentyFourth =
  BishopProperties.p<q⇒p⋆<q⋆
    0ℚᵘ twentyThreeTwentyFourth
    (ℚP.positive⁻¹ twentyThreeTwentyFourth)

positiveTwo : BishopReal.Positive (embed two)
positiveTwo =
  BishopProperties.0<x⇒posx
    (BishopProperties.p<q⇒p⋆<q⋆
      0ℚᵘ two (ℚP.positive⁻¹ two))

oneMinusSixthSquare : BishopReal.ℝ → BishopReal.ℝ
oneMinusSixthSquare value =
  BishopReal._-_ BishopReal.1ℝ
    (BishopReal._*_ (embed oneSixth) (square value))

oneMinusSixthSquareAboveTwentyThreeTwentyFourth :
  ∀ {dataSet value} →
  Concrete.ConcreteHalfBallSeriesInputs dataSet value →
  BishopReal._≤_
    (embed twentyThreeTwentyFourth)
    (oneMinusSixthSquare value)
oneMinusSixthSquareAboveTwentyThreeTwentyFourth {value = value} inputs =
  let
    scaledSquare =
      BishopProperties.*-monoˡ-≤-nonNeg
        (Cross.squareBelowQuarter inputs)
        Cross.oneSixthNonnegative
    shifted =
      BishopProperties.+-monoʳ-≤ BishopReal.1ℝ
        (BishopProperties.neg-mono-≤ scaledSquare)
  in
  BishopProperties.≤-respˡ-≃
    (let open BishopProperties.ℝ-Solver
     in solve 0
       (Κ (+ 23 / 24)
        ⊜ Κ (+ 1 / 1) ⊕
          (⊝ (Κ (+ 1 / 6) ⊗ Κ (+ 1 / 4))))
       BishopProperties.≃-refl)
    (BishopProperties.≤-respʳ-≃
      (let open BishopProperties.ℝ-Solver
       in solve 1
         (λ s →
           Κ (+ 1 / 1) ⊕ (⊝ (Κ (+ 1 / 6) ⊗ s))
           ⊜ Κ (+ 1 / 1) ⊖ (Κ (+ 1 / 6) ⊗ s))
         BishopProperties.≃-refl
         (square value))
      shifted)

oneMinusSixthSquarePositive :
  ∀ {dataSet value} →
  Concrete.ConcreteHalfBallSeriesInputs dataSet value →
  BishopReal.Positive (oneMinusSixthSquare value)
oneMinusSixthSquarePositive inputs =
  BishopProperties.0<x⇒posx
    (BishopProperties.<-≤-trans
      positiveTwentyThreeTwentyFourth
      (oneMinusSixthSquareAboveTwentyThreeTwentyFourth inputs))

cubicSineLowerPolynomial : BishopReal.ℝ → BishopReal.ℝ
cubicSineLowerPolynomial value =
  BishopReal._-_ value (Low.sineCubicTerm value)

cubicSineLowerFactors : ∀ value →
  BishopReal._≃_
    (cubicSineLowerPolynomial value)
    (BishopReal._*_ value (oneMinusSixthSquare value))
cubicSineLowerFactors value =
  let open BishopProperties.ℝ-Solver
  in solve 1
    (λ t →
      t ⊖ (Κ (+ 1 / 6) ⊗ ((t ⊗ t) ⊗ t))
      ⊜ t ⊗ (Κ (+ 1 / 1) ⊖ (Κ (+ 1 / 6) ⊗ (t ⊗ t))))
    BishopProperties.≃-refl value

cubicSineLowerPositive :
  ∀ {dataSet value} →
  Concrete.ConcreteHalfBallSeriesInputs dataSet value →
  BishopReal._<_ BishopReal.0ℝ value →
  BishopReal.Positive (cubicSineLowerPolynomial value)
cubicSineLowerPositive {value = value} inputs valuePositive =
  BishopProperties.pos-cong
    (BishopProperties.≃-symm (cubicSineLowerFactors value))
    (BishopProperties.posx,y⇒posx*y
      (BishopProperties.0<x⇒posx valuePositive)
      (oneMinusSixthSquarePositive inputs))

positiveSineOnPositiveHalfBall :
  ∀ {dataSet value} →
  Concrete.ConcreteHalfBallSeriesInputs dataSet value →
  BishopReal._<_ BishopReal.0ℝ value →
  BishopReal._<_ BishopReal.0ℝ (Elementary.bishopSin dataSet value)
positiveSineOnPositiveHalfBall inputs valuePositive =
  BishopProperties.<-≤-trans
    (BishopProperties.posx⇒0<x
      (cubicSineLowerPositive inputs valuePositive))
    (Low.sineCubicLower (Low.polynomialTaylorBounds inputs))

positiveSquare : ∀ {value} →
  BishopReal._<_ BishopReal.0ℝ value →
  BishopReal.Positive (square value)
positiveSquare valuePositive =
  BishopProperties.posx,y⇒posx*y
    (BishopProperties.0<x⇒posx valuePositive)
    (BishopProperties.0<x⇒posx valuePositive)

inverseDexpDenominatorPositive :
  ∀ {dataSet value} →
  Concrete.ConcreteHalfBallSeriesInputs dataSet value →
  BishopReal._<_ BishopReal.0ℝ value →
  BishopReal._<_ BishopReal.0ℝ
    (Cross.inverseDexpDenominator dataSet value)
inverseDexpDenominatorPositive inputs valuePositive =
  BishopProperties.posx⇒0<x
    (BishopProperties.posx,y⇒posx*y
      positiveTwo
      (BishopProperties.posx,y⇒posx*y
        (positiveSquare valuePositive)
        (BishopProperties.0<x⇒posx
          (positiveSineOnPositiveHalfBall inputs valuePositive))))

positiveDenominatorNonzero :
  ∀ {dataSet value} →
  Concrete.ConcreteHalfBallSeriesInputs dataSet value →
  BishopReal._<_ BishopReal.0ℝ value →
  BishopReal._≄_
    (Cross.inverseDexpDenominator dataSet value)
    BishopReal.0ℝ
positiveDenominatorNonzero inputs valuePositive =
  inj₂ (inverseDexpDenominatorPositive inputs valuePositive)

inverseDexpCoefficientPositive :
  ∀ {dataSet value} →
  (inputs : Concrete.ConcreteHalfBallSeriesInputs dataSet value) →
  (valuePositive : BishopReal._<_ BishopReal.0ℝ value) →
  BishopReal.ℝ
inverseDexpCoefficientPositive {dataSet} {value} inputs valuePositive =
  BishopReal._*_
    (Numerator.inverseDexpNumerator dataSet value)
    (BishopInverse._⁻¹
      (Cross.inverseDexpDenominator dataSet value)
      (positiveDenominatorNonzero inputs valuePositive))

record PositiveInverseDexpCoefficientBounds
    {dataSet : Elementary.BishopElementaryPowerSeriesData}
    {value : BishopReal.ℝ}
    (inputs : Concrete.ConcreteHalfBallSeriesInputs dataSet value)
    (valuePositive : BishopReal._<_ BishopReal.0ℝ value) : Set where
  field
    coefficientAboveOneTwelfth :
      BishopReal._≤_
        (embed oneTwelfth)
        (inverseDexpCoefficientPositive inputs valuePositive)
    coefficientBelowOneSixth :
      BishopReal._≤_
        (inverseDexpCoefficientPositive inputs valuePositive)
        (embed oneSixth)

open PositiveInverseDexpCoefficientBounds public

positiveInverseDexpCoefficientBounds :
  ∀ {dataSet value}
    (inputs : Concrete.ConcreteHalfBallSeriesInputs dataSet value)
    (valuePositive : BishopReal._<_ BishopReal.0ℝ value) →
  PositiveInverseDexpCoefficientBounds inputs valuePositive
positiveInverseDexpCoefficientBounds {dataSet} {value} inputs valuePositive =
  let
    denominator = Cross.inverseDexpDenominator dataSet value
    denominatorPositive = inverseDexpDenominatorPositive inputs valuePositive
    denominatorNonzero = positiveDenominatorNonzero inputs valuePositive
    denominatorInverse = BishopInverse._⁻¹ denominator denominatorNonzero
    denominatorInverseNonnegative =
      BishopProperties.pos⇒nonNeg
        (BishopInverse.posx⇒posx⁻¹ denominatorNonzero
          (BishopProperties.0<x⇒posx denominatorPositive))
    cross = Cross.crossMultipliedInverseDexpCoefficientBounds inputs
    lowerMultiplied =
      BishopProperties.*-monoʳ-≤-nonNeg
        (Cross.oneTwelfthDenominatorBelowNumerator cross)
        denominatorInverseNonnegative
    upperMultiplied =
      BishopProperties.*-monoʳ-≤-nonNeg
        (Cross.numeratorBelowOneSixthDenominator cross)
        denominatorInverseNonnegative
    cancelLeft :
      BishopReal._≃_
        (BishopReal._*_
          (BishopReal._*_ (embed oneTwelfth) denominator)
          denominatorInverse)
        (embed oneTwelfth)
    cancelLeft =
      BishopProperties.≃-trans
        (BishopProperties.*-assoc
          (embed oneTwelfth) denominator denominatorInverse)
        (BishopProperties.≃-trans
          (BishopProperties.*-congˡ
            (BishopInverse.*-inverseʳ denominator denominatorNonzero))
          (BishopProperties.*-identityʳ (embed oneTwelfth)))
    cancelRight :
      BishopReal._≃_
        (BishopReal._*_
          (BishopReal._*_ (embed oneSixth) denominator)
          denominatorInverse)
        (embed oneSixth)
    cancelRight =
      BishopProperties.≃-trans
        (BishopProperties.*-assoc
          (embed oneSixth) denominator denominatorInverse)
        (BishopProperties.≃-trans
          (BishopProperties.*-congˡ
            (BishopInverse.*-inverseʳ denominator denominatorNonzero))
          (BishopProperties.*-identityʳ (embed oneSixth)))
  in record
    { coefficientAboveOneTwelfth =
        BishopProperties.≤-respˡ-≃ cancelLeft lowerMultiplied
    ; coefficientBelowOneSixth =
        BishopProperties.≤-respʳ-≃ cancelRight upperMultiplied
    }

------------------------------------------------------------------------
-- Constructive endpoint split.  No equality decision is assumed.
------------------------------------------------------------------------

data NonnegativeRadiusCase (value : BishopReal.ℝ) : Set where
  zeroRadius : BishopReal._≃_ value BishopReal.0ℝ →
    NonnegativeRadiusCase value
  positiveRadius : BishopReal._<_ BishopReal.0ℝ value →
    NonnegativeRadiusCase value

inverseDexpCoefficientExtended :
  ∀ {dataSet value} →
  (inputs : Concrete.ConcreteHalfBallSeriesInputs dataSet value) →
  NonnegativeRadiusCase value →
  BishopReal.ℝ
inverseDexpCoefficientExtended inputs (zeroRadius valueZero) =
  embed oneTwelfth
inverseDexpCoefficientExtended inputs (positiveRadius valuePositive) =
  inverseDexpCoefficientPositive inputs valuePositive

inverseDexpCoefficientAtZero :
  ∀ {dataSet value}
    (inputs : Concrete.ConcreteHalfBallSeriesInputs dataSet value)
    (valueZero : BishopReal._≃_ value BishopReal.0ℝ) →
  BishopReal._≃_
    (inverseDexpCoefficientExtended inputs (zeroRadius valueZero))
    (embed oneTwelfth)
inverseDexpCoefficientAtZero inputs valueZero = BishopProperties.≃-refl

p33BishopPositiveSineLevel : ProofLevel
p33BishopPositiveSineLevel = machineChecked

p33BishopPositiveDenominatorLevel : ProofLevel
p33BishopPositiveDenominatorLevel = machineChecked

p33BishopPositiveCoefficientBoundLevel : ProofLevel
p33BishopPositiveCoefficientBoundLevel = machineChecked

p33BishopRemovableEndpointDefinitionLevel : ProofLevel
p33BishopRemovableEndpointDefinitionLevel = machineChecked
