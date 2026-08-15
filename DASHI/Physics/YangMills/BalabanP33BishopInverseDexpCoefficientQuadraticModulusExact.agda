module DASHI.Physics.YangMills.BalabanP33BishopInverseDexpCoefficientQuadraticModulusExact where

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
-- Convert the already-proved cross-multiplied endpoint estimate
--
--   0 <= n(t) - d(t)/12 <= (t^2/100) d(t)
--
-- into the actual inverse-dexp coefficient modulus on the positive half-ball.
-- Since d(t)>0, its Bishop inverse is positive and
--
--   beta(t) = n(t) d(t)^-1.
--
-- Multiplying by d(t)^-1 gives, without any real-number trichotomy,
--
--   0 <= beta(t) - 1/12 <= t^2/100.
--
-- This closes the analytic coefficient estimate itself.  A separate carrier
-- dictionary is still required if a downstream finite matrix insists on a
-- rational coefficient rather than a Bishop-real coefficient; that semantic
-- conversion is not silently asserted here.
------------------------------------------------------------------------

open import Data.Integer.Base using (+_; nonNeg)
open import Data.Rational.Unnormalised as ℚ using (ℚᵘ; _/_)

import Real as BishopReal
import RealProperties as BishopProperties
import Inverse as BishopInverse

import DASHI.Foundations.BishopPowerSeriesElementaryBridgeExact as Elementary
import DASHI.Physics.YangMills.BalabanBishopConcreteSineCosineInterlacingExact as Concrete
import DASHI.Physics.YangMills.BalabanP33BishopInverseDexpNumeratorExact as Numerator
import DASHI.Physics.YangMills.BalabanP33BishopInverseDexpCoefficientExact as Cross
import DASHI.Physics.YangMills.BalabanP33BishopInverseDexpPositiveDenominatorExact as Positive
import DASHI.Physics.YangMills.BalabanP33BishopInverseDexpActualEndpointModulusExact as Endpoint
open import DASHI.Physics.YangMills.CompactLieProofLevel

oneTwelfth oneHundred : ℚᵘ
oneTwelfth = + 1 / 12
oneHundred = + 1 / 100

embed : ℚᵘ → BishopReal.ℝ
embed = BishopReal._⋆

coefficientDifference :
  ∀ {dataSet value} →
  (inputs : Concrete.ConcreteHalfBallSeriesInputs dataSet value) →
  (valuePositive : BishopReal._<_ BishopReal.0ℝ value) →
  BishopReal.ℝ
coefficientDifference inputs valuePositive =
  BishopReal._-_
    (Positive.inverseDexpCoefficientPositive inputs valuePositive)
    (embed oneTwelfth)

endpointTimesInverseIsCoefficientDifference :
  ∀ {dataSet value}
    (inputs : Concrete.ConcreteHalfBallSeriesInputs dataSet value)
    (valuePositive : BishopReal._<_ BishopReal.0ℝ value) →
  BishopReal._≃_
    (BishopReal._*_
      (Endpoint.actualEndpointDefect dataSet value)
      (BishopInverse._⁻¹
        (Cross.inverseDexpDenominator dataSet value)
        (Positive.positiveDenominatorNonzero inputs valuePositive)))
    (coefficientDifference inputs valuePositive)
endpointTimesInverseIsCoefficientDifference {dataSet} {value}
    inputs valuePositive =
  let
    numerator = Numerator.inverseDexpNumerator dataSet value
    denominator = Cross.inverseDexpDenominator dataSet value
    denominatorNonzero = Positive.positiveDenominatorNonzero inputs valuePositive
    inverse = BishopInverse._⁻¹ denominator denominatorNonzero

    algebra :
      BishopReal._≃_
        (BishopReal._*_
          (BishopReal._-_
            numerator
            (BishopReal._*_ (embed oneTwelfth) denominator))
          inverse)
        (BishopReal._-_
          (BishopReal._*_ numerator inverse)
          (BishopReal._*_
            (embed oneTwelfth)
            (BishopReal._*_ denominator inverse)))
    algebra =
      let open BishopProperties.ℝ-Solver
      in solve 3
        (λ n d i →
          ((n ⊖ (Κ (+ 1 / 12) ⊗ d)) ⊗ i)
          ⊜ ((n ⊗ i) ⊖ (Κ (+ 1 / 12) ⊗ (d ⊗ i))))
        BishopProperties.≃-refl numerator denominator inverse

    cancel :
      BishopReal._≃_
        (BishopReal._-_
          (BishopReal._*_ numerator inverse)
          (BishopReal._*_
            (embed oneTwelfth)
            (BishopReal._*_ denominator inverse)))
        (BishopReal._-_
          (BishopReal._*_ numerator inverse)
          (embed oneTwelfth))
    cancel =
      BishopProperties.≃-trans
        (BishopProperties.+-congˡ
          (BishopProperties.neg-cong
            (BishopProperties.≃-trans
              (BishopProperties.*-congˡ
                (BishopInverse.*-inverseʳ denominator denominatorNonzero))
              (BishopProperties.*-identityʳ (embed oneTwelfth)))))
        BishopProperties.≃-refl
  in
  BishopProperties.≃-trans algebra cancel

coefficientDifferenceNonnegative :
  ∀ {dataSet value}
    (inputs : Concrete.ConcreteHalfBallSeriesInputs dataSet value)
    (valuePositive : BishopReal._<_ BishopReal.0ℝ value) →
  BishopReal._≤_ BishopReal.0ℝ
    (coefficientDifference inputs valuePositive)
coefficientDifferenceNonnegative {dataSet} {value} inputs valuePositive =
  let
    denominator = Cross.inverseDexpDenominator dataSet value
    denominatorNonzero = Positive.positiveDenominatorNonzero inputs valuePositive
    inverse = BishopInverse._⁻¹ denominator denominatorNonzero
    inverseNN =
      BishopProperties.pos⇒nonNeg
        (BishopInverse.posx⇒posx⁻¹ denominatorNonzero
          (BishopProperties.0<x⇒posx
            (Positive.inverseDexpDenominatorPositive inputs valuePositive)))
    scaled = BishopProperties.*-monoʳ-≤-nonNeg
      (Endpoint.actualEndpointDefectNonnegative inputs)
      inverseNN
  in
  BishopProperties.≤-respʳ-≃
    (endpointTimesInverseIsCoefficientDifference inputs valuePositive)
    (BishopProperties.≤-respˡ-≃
      (BishopProperties.≃-symm (BishopProperties.zero-productˡ inverse))
      scaled)

quadraticScale : BishopReal.ℝ → BishopReal.ℝ
quadraticScale value =
  BishopReal._*_ (embed oneHundred) (Endpoint.square value)

scaledQuadraticDenominatorCancels :
  ∀ {dataSet value}
    (inputs : Concrete.ConcreteHalfBallSeriesInputs dataSet value)
    (valuePositive : BishopReal._<_ BishopReal.0ℝ value) →
  BishopReal._≃_
    (BishopReal._*_
      (Endpoint.quadraticDenominatorScale dataSet value)
      (BishopInverse._⁻¹
        (Cross.inverseDexpDenominator dataSet value)
        (Positive.positiveDenominatorNonzero inputs valuePositive)))
    (quadraticScale value)
scaledQuadraticDenominatorCancels {dataSet} {value} inputs valuePositive =
  let
    denominator = Cross.inverseDexpDenominator dataSet value
    denominatorNonzero = Positive.positiveDenominatorNonzero inputs valuePositive
    inverse = BishopInverse._⁻¹ denominator denominatorNonzero
    scale = quadraticScale value
    algebra :
      BishopReal._≃_
        (BishopReal._*_
          (BishopReal._*_ scale denominator)
          inverse)
        (BishopReal._*_
          scale (BishopReal._*_ denominator inverse))
    algebra = BishopProperties.*-assoc scale denominator inverse
  in
  BishopProperties.≃-trans algebra
    (BishopProperties.≃-trans
      (BishopProperties.*-congˡ
        (BishopInverse.*-inverseʳ denominator denominatorNonzero))
      (BishopProperties.*-identityʳ scale))

coefficientDifferenceQuadraticModulus :
  ∀ {dataSet value}
    (inputs : Concrete.ConcreteHalfBallSeriesInputs dataSet value)
    (valuePositive : BishopReal._<_ BishopReal.0ℝ value) →
  BishopReal._≤_
    (coefficientDifference inputs valuePositive)
    (quadraticScale value)
coefficientDifferenceQuadraticModulus {dataSet} {value} inputs valuePositive =
  let
    denominator = Cross.inverseDexpDenominator dataSet value
    denominatorNonzero = Positive.positiveDenominatorNonzero inputs valuePositive
    inverse = BishopInverse._⁻¹ denominator denominatorNonzero
    inverseNN =
      BishopProperties.pos⇒nonNeg
        (BishopInverse.posx⇒posx⁻¹ denominatorNonzero
          (BishopProperties.0<x⇒posx
            (Positive.inverseDexpDenominatorPositive inputs valuePositive)))
    scaled = BishopProperties.*-monoʳ-≤-nonNeg
      (Endpoint.actualEndpointDefectQuadraticModulus inputs)
      inverseNN
  in
  BishopProperties.≤-respʳ-≃
    (scaledQuadraticDenominatorCancels inputs valuePositive)
    (BishopProperties.≤-respˡ-≃
      (endpointTimesInverseIsCoefficientDifference inputs valuePositive)
      scaled)

record PositiveCoefficientQuadraticModulus
    {dataSet : Elementary.BishopElementaryPowerSeriesData}
    {value : BishopReal.ℝ}
    (inputs : Concrete.ConcreteHalfBallSeriesInputs dataSet value)
    (valuePositive : BishopReal._<_ BishopReal.0ℝ value) : Set where
  field
    differenceNonnegative :
      BishopReal._≤_ BishopReal.0ℝ
        (coefficientDifference inputs valuePositive)
    differenceBelowQuadratic :
      BishopReal._≤_
        (coefficientDifference inputs valuePositive)
        (quadraticScale value)

positiveCoefficientQuadraticModulus :
  ∀ {dataSet value}
    (inputs : Concrete.ConcreteHalfBallSeriesInputs dataSet value)
    (valuePositive : BishopReal._<_ BishopReal.0ℝ value) →
  PositiveCoefficientQuadraticModulus inputs valuePositive
positiveCoefficientQuadraticModulus inputs valuePositive = record
  { PositiveCoefficientQuadraticModulus.differenceNonnegative =
      coefficientDifferenceNonnegative inputs valuePositive
  ; PositiveCoefficientQuadraticModulus.differenceBelowQuadratic =
      coefficientDifferenceQuadraticModulus inputs valuePositive
  }

p33BishopInverseDexpCoefficientDifferenceNonnegativeLevel : ProofLevel
p33BishopInverseDexpCoefficientDifferenceNonnegativeLevel = machineChecked

p33BishopInverseDexpCoefficientQuadraticModulusLevel : ProofLevel
p33BishopInverseDexpCoefficientQuadraticModulusLevel = machineChecked
