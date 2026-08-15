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
-- Turn the checked cross-multiplied endpoint estimate
--
--   0 <= n(t)-d(t)/12 <= (t^2/100)d(t)
--
-- into the actual positive-radius coefficient estimate
--
--   0 <= beta(t)-1/12 <= t^2/100,
--   beta(t)=n(t)d(t)^-1.
--
-- The proof stays constructive: d(t)>0 was already proved on the positive
-- half-ball, so multiplication by the positive Bishop inverse preserves order.
-- No real trichotomy and no rational approximation of beta(t) is introduced.
-- A later finite-matrix dictionary must therefore preserve the distinction
-- between this Bishop-real coefficient and any rational certificate carrier.
------------------------------------------------------------------------

open import Data.Integer.Base using (+_)
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

quadraticScale : BishopReal.ℝ → BishopReal.ℝ
quadraticScale value =
  BishopReal._*_ (embed oneHundred) (Endpoint.square value)

coefficientDifference :
  ∀ {dataSet value} →
  (inputs : Concrete.ConcreteHalfBallSeriesInputs dataSet value) →
  (valuePositive : BishopReal._<_ BishopReal.0ℝ value) →
  BishopReal.ℝ
coefficientDifference inputs valuePositive =
  BishopReal._-_
    (Positive.inverseDexpCoefficientPositive inputs valuePositive)
    (embed oneTwelfth)

coefficientDifferenceNonnegative :
  ∀ {dataSet value}
    (inputs : Concrete.ConcreteHalfBallSeriesInputs dataSet value)
    (valuePositive : BishopReal._<_ BishopReal.0ℝ value) →
  BishopReal._≤_ BishopReal.0ℝ
    (coefficientDifference inputs valuePositive)
coefficientDifferenceNonnegative inputs valuePositive =
  let
    bounds = Positive.positiveInverseDexpCoefficientBounds inputs valuePositive
    beta = Positive.inverseDexpCoefficientPositive inputs valuePositive
    shifted = BishopProperties.+-monoʳ-≤
      (BishopReal.- (embed oneTwelfth))
      (Positive.coefficientAboveOneTwelfth bounds)
    leftExact :
      BishopReal._≃_
        (BishopReal._+_ (embed oneTwelfth)
          (BishopReal.- (embed oneTwelfth)))
        BishopReal.0ℝ
    leftExact =
      let open BishopProperties.ℝ-Solver
      in solve 0
        ((Κ (+ 1 / 12)) ⊕ (⊝ (Κ (+ 1 / 12))) ⊜ Κ (+ 0 / 1))
        BishopProperties.≃-refl
    rightExact :
      BishopReal._≃_
        (BishopReal._+_ beta (BishopReal.- (embed oneTwelfth)))
        (coefficientDifference inputs valuePositive)
    rightExact =
      let open BishopProperties.ℝ-Solver
      in solve 1
        (λ b → b ⊕ (⊝ (Κ (+ 1 / 12))) ⊜ b ⊖ Κ (+ 1 / 12))
        BishopProperties.≃-refl beta
  in
  BishopProperties.≤-respʳ-≃ rightExact
    (BishopProperties.≤-respˡ-≃ leftExact shifted)

numeratorBelowCoefficientEnvelopeTimesDenominator :
  ∀ {dataSet value}
    (inputs : Concrete.ConcreteHalfBallSeriesInputs dataSet value) →
  BishopReal._≤_
    (Numerator.inverseDexpNumerator dataSet value)
    (BishopReal._*_
      (BishopReal._+_ (embed oneTwelfth) (quadraticScale value))
      (Cross.inverseDexpDenominator dataSet value))
numeratorBelowCoefficientEnvelopeTimesDenominator {dataSet} {value} inputs =
  let
    n = Numerator.inverseDexpNumerator dataSet value
    d = Cross.inverseDexpDenominator dataSet value
    q = quadraticScale value
    endpointUpper = Endpoint.actualEndpointDefectQuadraticModulus inputs
    added = BishopProperties.+-monoʳ-≤
      (BishopReal._*_ (embed oneTwelfth) d)
      endpointUpper

    leftExact :
      BishopReal._≃_
        (BishopReal._+_
          (BishopReal._*_ (embed oneTwelfth) d)
          (Endpoint.actualEndpointDefect dataSet value))
        n
    leftExact =
      let open BishopProperties.ℝ-Solver
      in solve 2
        (λ numerator denominator →
          ((Κ (+ 1 / 12) ⊗ denominator)
            ⊕ (numerator ⊖ (Κ (+ 1 / 12) ⊗ denominator)))
          ⊜ numerator)
        BishopProperties.≃-refl n d

    rightExact :
      BishopReal._≃_
        (BishopReal._+_
          (BishopReal._*_ (embed oneTwelfth) d)
          (Endpoint.quadraticDenominatorScale dataSet value))
        (BishopReal._*_
          (BishopReal._+_ (embed oneTwelfth) q) d)
    rightExact =
      let open BishopProperties.ℝ-Solver
      in solve 2
        (λ denominator scale →
          ((Κ (+ 1 / 12) ⊗ denominator)
            ⊕ (scale ⊗ denominator))
          ⊜ ((Κ (+ 1 / 12) ⊕ scale) ⊗ denominator))
        BishopProperties.≃-refl d q
  in
  BishopProperties.≤-respʳ-≃ rightExact
    (BishopProperties.≤-respˡ-≃ leftExact added)

coefficientBelowOneTwelfthPlusQuadratic :
  ∀ {dataSet value}
    (inputs : Concrete.ConcreteHalfBallSeriesInputs dataSet value)
    (valuePositive : BishopReal._<_ BishopReal.0ℝ value) →
  BishopReal._≤_
    (Positive.inverseDexpCoefficientPositive inputs valuePositive)
    (BishopReal._+_ (embed oneTwelfth) (quadraticScale value))
coefficientBelowOneTwelfthPlusQuadratic {dataSet} {value}
    inputs valuePositive =
  let
    d = Cross.inverseDexpDenominator dataSet value
    denominatorNonzero = Positive.positiveDenominatorNonzero inputs valuePositive
    inverse = BishopInverse._⁻¹ d denominatorNonzero
    inverseNonnegative =
      BishopProperties.pos⇒nonNeg
        (BishopInverse.posx⇒posx⁻¹ denominatorNonzero
          (BishopProperties.0<x⇒posx
            (Positive.inverseDexpDenominatorPositive inputs valuePositive)))

    numeratorUpper =
      numeratorBelowCoefficientEnvelopeTimesDenominator inputs
    scaled = BishopProperties.*-monoʳ-≤-nonNeg
      numeratorUpper inverseNonnegative

    envelope = BishopReal._+_ (embed oneTwelfth) (quadraticScale value)
    cancelRight :
      BishopReal._≃_
        (BishopReal._*_
          (BishopReal._*_ envelope d) inverse)
        envelope
    cancelRight =
      BishopProperties.≃-trans
        (BishopProperties.*-assoc envelope d inverse)
        (BishopProperties.≃-trans
          (BishopProperties.*-congˡ
            (BishopInverse.*-inverseʳ d denominatorNonzero))
          (BishopProperties.*-identityʳ envelope))
  in
  BishopProperties.≤-respʳ-≃ cancelRight scaled

coefficientDifferenceQuadraticModulus :
  ∀ {dataSet value}
    (inputs : Concrete.ConcreteHalfBallSeriesInputs dataSet value)
    (valuePositive : BishopReal._<_ BishopReal.0ℝ value) →
  BishopReal._≤_
    (coefficientDifference inputs valuePositive)
    (quadraticScale value)
coefficientDifferenceQuadraticModulus {value = value} inputs valuePositive =
  let
    beta = Positive.inverseDexpCoefficientPositive inputs valuePositive
    q = quadraticScale value
    shifted = BishopProperties.+-monoʳ-≤
      (BishopReal.- (embed oneTwelfth))
      (coefficientBelowOneTwelfthPlusQuadratic inputs valuePositive)
    leftExact :
      BishopReal._≃_
        (BishopReal._+_ beta (BishopReal.- (embed oneTwelfth)))
        (coefficientDifference inputs valuePositive)
    leftExact =
      let open BishopProperties.ℝ-Solver
      in solve 1
        (λ b → b ⊕ (⊝ (Κ (+ 1 / 12))) ⊜ b ⊖ Κ (+ 1 / 12))
        BishopProperties.≃-refl beta
    rightExact :
      BishopReal._≃_
        (BishopReal._+_
          (BishopReal._+_ (embed oneTwelfth) q)
          (BishopReal.- (embed oneTwelfth)))
        q
    rightExact =
      let open BishopProperties.ℝ-Solver
      in solve 1
        (λ scale →
          ((Κ (+ 1 / 12) ⊕ scale) ⊕ (⊝ (Κ (+ 1 / 12)))
          ⊜ scale)
        BishopProperties.≃-refl q
  in
  BishopProperties.≤-respʳ-≃ rightExact
    (BishopProperties.≤-respˡ-≃ leftExact shifted)

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
