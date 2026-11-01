module DASHI.Physics.YangMills.BalabanCMP109BishopPrincipalLogSymmetricCoefficientExact where

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
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- DASHI CONTRIBUTION
--
-- Turn the previously proved constructive inverse-dexp coefficient estimate
-- into the coercive scalar used by the principal-log Jacobian.  On su(2), in
-- the plane orthogonal to the logarithm axis,
--
--     dexp_X^-1 = I +/- (1/2) ad_X + beta(t) ad_X^2,
--
-- and ad_X^2 acts as -t^2.  Hence the symmetric plane coefficient is
--
--     a(t) = 1 - beta(t) t^2.
--
-- The checked Bishop bounds beta(t) <= 1/6 and t^2 <= 1/4 imply
--
--     a(t) >= 1 - (1/6)(1/4) = 23/24
--
-- on the entire constructive half ball, with the removable t=0 branch handled
-- explicitly.  This is the concrete positive coercivity constant requested by
-- both the Federbush equation-(0.11) solve and equation-(0.12) log derivative.
------------------------------------------------------------------------

open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised as ℚ using (ℚᵘ; _≤_; _/_)
import Data.Rational.Unnormalised.Properties as ℚP
open ℚP using (_≤?_)
open import Relation.Nullary.Decidable.Core using (toWitness)

import Real as BishopReal
import RealProperties as BishopProperties

import DASHI.Physics.YangMills.BalabanBishopConcreteSineCosineInterlacingExact as Concrete
import DASHI.Physics.YangMills.BalabanP33BishopInverseDexpCoefficientExact as Cross
import DASHI.Physics.YangMills.BalabanP33BishopInverseDexpPositiveDenominatorExact as Positive
open import DASHI.Physics.YangMills.CompactLieProofLevel

twentyThreeTwentyFourth : ℚᵘ
twentyThreeTwentyFourth = + 23 / 24

embed : ℚᵘ → BishopReal.ℝ
embed = BishopReal._⋆

square : BishopReal.ℝ → BishopReal.ℝ
square value = BishopReal._*_ value value

principalLogSymmetricCoefficient :
  ∀ {dataSet value} →
  (inputs : Concrete.ConcreteHalfBallSeriesInputs dataSet value) →
  Positive.NonnegativeRadiusCase value → BishopReal.ℝ
principalLogSymmetricCoefficient {value = value} inputs radiusCase =
  BishopReal._-_
    BishopReal.1ℝ
    (BishopReal._*_
      (Positive.inverseDexpCoefficientExtended inputs radiusCase)
      (square value))

positiveCaseSymmetricCoefficientAboveTwentyThreeTwentyFourth :
  ∀ {dataSet value}
    (inputs : Concrete.ConcreteHalfBallSeriesInputs dataSet value)
    (valuePositive : BishopReal._<_ BishopReal.0ℝ value) →
  BishopReal._≤_
    (embed twentyThreeTwentyFourth)
    (principalLogSymmetricCoefficient
      inputs (Positive.positiveRadius valuePositive))
positiveCaseSymmetricCoefficientAboveTwentyThreeTwentyFourth
    {value = value} inputs valuePositive =
  let
    coefficientBounds =
      Positive.positiveInverseDexpCoefficientBounds inputs valuePositive

    squareNonnegative : BishopReal.NonNegative (square value)
    squareNonnegative =
      Cross.squareNonnegativeFromInput value
        (Concrete.valueNonnegative inputs)

    scaledCoefficient :
      BishopReal._≤_
        (BishopReal._*_
          (Positive.inverseDexpCoefficientPositive inputs valuePositive)
          (square value))
        (BishopReal._*_
          (embed Positive.oneSixth)
          (square value))
    scaledCoefficient =
      BishopProperties.*-monoʳ-≤-nonNeg
        (Positive.coefficientBelowOneSixth coefficientBounds)
        squareNonnegative

    shifted :
      BishopReal._≤_
        (BishopReal._-_
          BishopReal.1ℝ
          (BishopReal._*_
            (embed Positive.oneSixth) (square value)))
        (BishopReal._-_
          BishopReal.1ℝ
          (BishopReal._*_
            (Positive.inverseDexpCoefficientPositive inputs valuePositive)
            (square value)))
    shifted =
      BishopProperties.+-monoʳ-≤ BishopReal.1ℝ
        (BishopProperties.neg-mono-≤ scaledCoefficient)
  in
  BishopProperties.≤-trans
    (Positive.oneMinusSixthSquareAboveTwentyThreeTwentyFourth inputs)
    shifted

zeroCaseSymmetricCoefficientIsOne :
  ∀ {dataSet value}
    (inputs : Concrete.ConcreteHalfBallSeriesInputs dataSet value)
    (valueZero : BishopReal._≃_ value BishopReal.0ℝ) →
  BishopReal._≃_
    (principalLogSymmetricCoefficient
      inputs (Positive.zeroRadius valueZero))
    BishopReal.1ℝ
zeroCaseSymmetricCoefficientIsOne {value = value} inputs valueZero =
  let open BishopProperties.ℝ-Solver
  in solve 1
    (λ t →
      Κ (+ 1 / 1)
        ⊖ (Κ (+ 1 / 12) ⊗ (t ⊗ t))
      ⊜ Κ (+ 1 / 1))
    valueZero

twentyThreeTwentyFourthBelowOne :
  twentyThreeTwentyFourth ≤ (+ 1 / 1)
twentyThreeTwentyFourthBelowOne =
  toWitness {a? = twentyThreeTwentyFourth ≤? (+ 1 / 1)} _

zeroCaseSymmetricCoefficientAboveTwentyThreeTwentyFourth :
  ∀ {dataSet value}
    (inputs : Concrete.ConcreteHalfBallSeriesInputs dataSet value)
    (valueZero : BishopReal._≃_ value BishopReal.0ℝ) →
  BishopReal._≤_
    (embed twentyThreeTwentyFourth)
    (principalLogSymmetricCoefficient
      inputs (Positive.zeroRadius valueZero))
zeroCaseSymmetricCoefficientAboveTwentyThreeTwentyFourth inputs valueZero =
  BishopProperties.≤-respʳ-≃
    (BishopProperties.≃-symm
      (zeroCaseSymmetricCoefficientIsOne inputs valueZero))
    (BishopProperties.p≤q⇒p⋆≤q⋆
      twentyThreeTwentyFourth (+ 1 / 1)
      twentyThreeTwentyFourthBelowOne)

principalLogSymmetricCoefficientAboveTwentyThreeTwentyFourth :
  ∀ {dataSet value}
    (inputs : Concrete.ConcreteHalfBallSeriesInputs dataSet value)
    (radiusCase : Positive.NonnegativeRadiusCase value) →
  BishopReal._≤_
    (embed twentyThreeTwentyFourth)
    (principalLogSymmetricCoefficient inputs radiusCase)
principalLogSymmetricCoefficientAboveTwentyThreeTwentyFourth
    inputs (Positive.zeroRadius valueZero) =
  zeroCaseSymmetricCoefficientAboveTwentyThreeTwentyFourth inputs valueZero
principalLogSymmetricCoefficientAboveTwentyThreeTwentyFourth
    inputs (Positive.positiveRadius valuePositive) =
  positiveCaseSymmetricCoefficientAboveTwentyThreeTwentyFourth inputs valuePositive

cmp109BishopPrincipalLogSymmetricCoefficientLevel : ProofLevel
cmp109BishopPrincipalLogSymmetricCoefficientLevel = machineChecked

cmp109BishopPrincipalLogCoercivityFloorTwentyThreeTwentyFourthLevel : ProofLevel
cmp109BishopPrincipalLogCoercivityFloorTwentyThreeTwentyFourthLevel = machineChecked
