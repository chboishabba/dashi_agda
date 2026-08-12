module DASHI.Physics.YangMills.BalabanCMP109BishopInverseDexpCoefficientEndpointModulusExact where

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
-- Convert the already checked cross-multiplied endpoint theorem into a bound
-- for the *actual* inverse-dexp Bernoulli coefficient.  On the positive half
-- ball, with
--
--   beta(t) = n(t) / d(t),
--
-- the repository proves
--
--   0 <= n(t) - d(t)/12 <= (t^2/100) d(t)
--
-- and d(t)>0.  Positive-denominator cancellation therefore gives
--
--   0 <= beta(t) - 1/12 <= t^2/100.
--
-- The zero-radius branch is exactly beta(0)=1/12.  This is the regular
-- endpoint coefficient modulus needed by the ad_X-polynomial representation;
-- no normalized axis X/|X| is introduced.
------------------------------------------------------------------------

open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised as ℚ using (ℚᵘ; _/_)

import Real as BishopReal
import RealProperties as BishopProperties
import Inverse as BishopInverse

import DASHI.Physics.YangMills.BalabanBishopConcreteSineCosineInterlacingExact as Concrete
import DASHI.Physics.YangMills.BalabanP33BishopInverseDexpCoefficientExact as Cross
import DASHI.Physics.YangMills.BalabanP33BishopInverseDexpPositiveDenominatorExact as Positive
import DASHI.Physics.YangMills.BalabanP33BishopInverseDexpActualEndpointModulusExact as Endpoint
open import DASHI.Physics.YangMills.CompactLieProofLevel

oneTwelfth oneHundred : ℚᵘ
oneTwelfth = + 1 / 12
oneHundred = + 1 / 100

embed : ℚᵘ → BishopReal.ℝ
embed = BishopReal._⋆

square : BishopReal.ℝ → BishopReal.ℝ
square value = BishopReal._*_ value value

coefficientEndpointDefect :
  ∀ {dataSet value} →
  (inputs : Concrete.ConcreteHalfBallSeriesInputs dataSet value) →
  (valuePositive : BishopReal._<_ BishopReal.0ℝ value) →
  BishopReal.ℝ
coefficientEndpointDefect inputs valuePositive =
  BishopReal._-_
    (Positive.inverseDexpCoefficientPositive inputs valuePositive)
    (embed oneTwelfth)

record PositiveCoefficientEndpointModulus
    {dataSet value}
    (inputs : Concrete.ConcreteHalfBallSeriesInputs dataSet value)
    (valuePositive : BishopReal._<_ BishopReal.0ℝ value) : Set where
  field
    defectNonnegative :
      BishopReal._≤_ BishopReal.0ℝ
        (coefficientEndpointDefect inputs valuePositive)
    defectQuadraticUpper :
      BishopReal._≤_
        (coefficientEndpointDefect inputs valuePositive)
        (BishopReal._*_ (embed oneHundred) (square value))

open PositiveCoefficientEndpointModulus public

positiveCoefficientEndpointModulus :
  ∀ {dataSet value}
    (inputs : Concrete.ConcreteHalfBallSeriesInputs dataSet value)
    (valuePositive : BishopReal._<_ BishopReal.0ℝ value) →
  PositiveCoefficientEndpointModulus inputs valuePositive
positiveCoefficientEndpointModulus {dataSet} {value} inputs valuePositive =
  let
    denominator = Cross.inverseDexpDenominator dataSet value
    numerator = Endpoint.Numerator.inverseDexpNumerator dataSet value
    denominatorNonzero = Positive.positiveDenominatorNonzero inputs valuePositive
    denominatorPositive = Positive.inverseDexpDenominatorPositive inputs valuePositive
    denominatorInverse = BishopInverse._⁻¹ denominator denominatorNonzero
    denominatorInverseNonnegative =
      BishopProperties.pos⇒nonNeg
        (BishopInverse.posx⇒posx⁻¹ denominatorNonzero
          (BishopProperties.0<x⇒posx denominatorPositive))

    multipliedUpper =
      BishopProperties.*-monoʳ-≤-nonNeg
        (Endpoint.actualEndpointDefectQuadraticModulus inputs)
        denominatorInverseNonnegative

    denominatorCancellation =
      BishopInverse.*-inverseʳ denominator denominatorNonzero

    leftCancel :
      BishopReal._≃_
        (BishopReal._*_
          (Endpoint.actualEndpointDefect dataSet value)
          denominatorInverse)
        (coefficientEndpointDefect inputs valuePositive)
    leftCancel =
      let open BishopProperties.ℝ-Solver
      in solve 4
        (λ n d dinv beta →
          ((n ⊖ (Κ (+ 1 / 12) ⊗ d)) ⊗ dinv)
          ⊜ (beta ⊖ Κ (+ 1 / 12)))
        BishopProperties.≃-refl
        numerator denominator denominatorInverse
        (Positive.inverseDexpCoefficientPositive inputs valuePositive)
        denominatorCancellation

    rightCancel :
      BishopReal._≃_
        (BishopReal._*_
          (Endpoint.quadraticDenominatorScale dataSet value)
          denominatorInverse)
        (BishopReal._*_ (embed oneHundred) (square value))
    rightCancel =
      let open BishopProperties.ℝ-Solver
      in solve 3
        (λ t d dinv →
          (((Κ (+ 1 / 100) ⊗ (t ⊗ t)) ⊗ d) ⊗ dinv)
          ⊜ (Κ (+ 1 / 100) ⊗ (t ⊗ t)))
        BishopProperties.≃-refl
        value denominator denominatorInverse
        denominatorCancellation

    upper =
      BishopProperties.≤-respʳ-≃ rightCancel
        (BishopProperties.≤-respˡ-≃ leftCancel multipliedUpper)

    coefficientBounds =
      Positive.positiveInverseDexpCoefficientBounds inputs valuePositive
    lower =
      Cross.nonnegativeDifferenceGivesOrder
        (Positive.coefficientAboveOneTwelfth coefficientBounds)
  in record
    { defectNonnegative = lower
    ; defectQuadraticUpper = upper
    }

zeroCoefficientEndpointDefect :
  ∀ {dataSet value}
    (inputs : Concrete.ConcreteHalfBallSeriesInputs dataSet value)
    (valueZero : BishopReal._≃_ value BishopReal.0ℝ) →
  BishopReal._≃_
    (BishopReal._-_
      (Positive.inverseDexpCoefficientExtended
        inputs (Positive.zeroRadius valueZero))
      (embed oneTwelfth))
    BishopReal.0ℝ
zeroCoefficientEndpointDefect inputs valueZero =
  let open BishopProperties.ℝ-Solver
  in solve 0
    ((Κ (+ 1 / 12) ⊖ Κ (+ 1 / 12)) ⊜ Κ (+ 0 / 1))
    BishopProperties.≃-refl

cmp109BishopInverseDexpEndpointCoefficientModulusLevel : ProofLevel
cmp109BishopInverseDexpEndpointCoefficientModulusLevel = machineChecked

cmp109BishopInverseDexpZeroEndpointExactLevel : ProofLevel
cmp109BishopInverseDexpZeroEndpointExactLevel = machineChecked
