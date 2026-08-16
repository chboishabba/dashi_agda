module DASHI.Physics.YangMills.BalabanBishopSineTwoBallCubicLowerExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE / CONSTRUCTIVE BACKEND
--
-- Zachary Murray,
-- "Constructive Analysis in the Agda Proof Assistant",
-- B.Sc. Honours thesis, Dalhousie University, 2022.
-- arXiv:2205.08354. No DOI assigned.
--
-- Code continuation: Viktor Csimma, viktorcsimma/bishop, pinned by DASHI at
-- vendor/bishop commit 240e38c7f6938f20f865b1f956c5f084da48bd54.
--
-- APPLICATION SOURCE
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- DASHI CONTRIBUTION
--
-- The existing constructive sine/cosine interlacing was deliberately proved
-- only on |t|<=1/2 because that is the sharp local-chart domain needed by P33.
-- The Brillouin denominator lane needs a different fact: one coarse positive
-- lower bound for sin(t) on the first quadrant, with t<2.  Reusing the exact
-- factorial recurrence, the sine magnitudes satisfy
--
--   m_{n+1} <= (|t|^2/6) m_n <= (2/3)m_n <= m_n,   |t|<=2.
--
-- Thus the sine series alone is alternating and decreasing on the full radius
-- two ball.  The same interlacing proof therefore yields the machine-relevant
-- cubic lower bound
--
--                 t - t^3/6 <= sin(t),
--
-- for 0<=t and |t|<=2.  No trigonometric oracle, differentiability argument,
-- or classical monotonicity theorem is imported.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (zero; suc)
open import Data.Integer.Base using (+_; nonNeg)
open import Data.Rational.Unnormalised as ℚ using (ℚᵘ; 0ℚᵘ; _/_)
import Data.Rational.Unnormalised.Properties as ℚP

import Real as BishopReal
import RealProperties as BishopProperties

import DASHI.Foundations.BishopPowerSeriesElementaryBridgeExact as Elementary
import DASHI.Physics.YangMills.BalabanBishopConcreteFactorialCoefficientDischargeExact as Factorial
import DASHI.Physics.YangMills.BalabanBishopFactorialPowerRecurrenceExact as Recurrence
import DASHI.Physics.YangMills.BalabanBishopConcreteHalfRadiusRatiosExact as Ratios
import DASHI.Physics.YangMills.BalabanBishopConcreteHalfBallSquareExact as Square
import DASHI.Physics.YangMills.BalabanBishopConcreteSineCosineTermParityExact as Terms
import DASHI.Physics.YangMills.BalabanBishopConcreteSineCosineInterlacingExact as Concrete
import DASHI.Physics.YangMills.BalabanBishopAlternatingInterlacingFromDecreasingTermsExact as Alternating
import DASHI.Physics.YangMills.BalabanBishopAlternatingBracketFromMonotoneLimitsExact as Interlacing
import DASHI.Physics.YangMills.BalabanP33BishopLowOrderTaylorBracketsExact as Low
import DASHI.Physics.YangMills.BalabanP33BishopTaylorPolynomialFormExact as Polynomial
import DASHI.Physics.YangMills.BalabanP33BishopInverseDexpCoefficientExact as Order
open import DASHI.Physics.YangMills.CompactLieProofLevel

two four twoThird oneThird : ℚᵘ
two = + 2 / 1
four = + 4 / 1
twoThird = + 2 / 3
oneThird = + 1 / 3

bishopTwo bishopFour bishopTwoThird bishopOneThird : BishopReal.ℝ
bishopTwo = BishopReal._⋆ two
bishopFour = BishopReal._⋆ four
bishopTwoThird = BishopReal._⋆ twoThird
bishopOneThird = BishopReal._⋆ oneThird

bishopTwoNonnegative : BishopReal.NonNegative bishopTwo
bishopTwoNonnegative = Order.embeddedRationalNonnegative two nonNeg

bishopOneSixthNonnegative : BishopReal.NonNegative Ratios.bishopOneSixth
bishopOneSixthNonnegative = Ratios.bishopOneSixthNonnegative

bishopTwoSquareEquivalentFour :
  BishopReal._≃_ (BishopReal._*_ bishopTwo bishopTwo) bishopFour
bishopTwoSquareEquivalentFour =
  let open BishopProperties.ℝ-Solver
  in solve 0
      (Κ two ⊗ Κ two ⊜ Κ four)
      BishopProperties.≃-refl

magnitudeSquareBelowFour :
  ∀ value →
  BishopReal._≤_ (BishopReal.∣_∣ value) bishopTwo →
  BishopReal._≤_ (Square.bishopMagnitudeSquare value) bishopFour
magnitudeSquareBelowFour value insideTwo =
  BishopProperties.≤-respʳ-≃ bishopTwoSquareEquivalentFour
    (BishopProperties.*-mono-≤
      (BishopProperties.nonNeg∣x∣ value)
      (BishopProperties.nonNeg∣x∣ value)
      insideTwo insideTwo)

fourTimesSixthEquivalentTwoThird :
  BishopReal._≃_
    (BishopReal._*_ bishopFour Ratios.bishopOneSixth)
    bishopTwoThird
fourTimesSixthEquivalentTwoThird =
  let open BishopProperties.ℝ-Solver
  in solve 0
      (Κ four ⊗ Κ Ratios.oneSixth ⊜ Κ twoThird)
      BishopProperties.≃-refl

sineRatioBelowTwoThird :
  ∀ value →
  BishopReal._≤_ (BishopReal.∣_∣ value) bishopTwo →
  BishopReal._≤_
    (Ratios.bishopSineSuccessiveMagnitudeRatio value)
    bishopTwoThird
sineRatioBelowTwoThird value insideTwo =
  BishopProperties.≤-respʳ-≃ fourTimesSixthEquivalentTwoThird
    (BishopProperties.*-monoʳ-≤-nonNeg
      (magnitudeSquareBelowFour value insideTwo)
      bishopOneSixthNonnegative)

oneMinusTwoThirdEquivalentOneThird :
  BishopReal._≃_
    (BishopReal._-_ BishopReal.1ℝ bishopTwoThird)
    bishopOneThird
oneMinusTwoThirdEquivalentOneThird =
  let open BishopProperties.ℝ-Solver
  in solve 0
      (Κ (+ 1 / 1) ⊖ Κ twoThird ⊜ Κ oneThird)
      BishopProperties.≃-refl

bishopTwoThirdBelowOne : BishopReal._≤_ bishopTwoThird BishopReal.1ℝ
bishopTwoThirdBelowOne =
  Order.nonnegativeDifferenceGivesOrder
    (BishopProperties.≤-respʳ-≃
      (BishopProperties.≃-symm oneMinusTwoThirdEquivalentOneThird)
      (BishopProperties.nonNegx⇒0≤x
        (Order.embeddedRationalNonnegative oneThird nonNeg)))

sineMagnitudeDecreasingTwoBall :
  ∀ value →
  BishopReal._≤_ (BishopReal.∣_∣ value) bishopTwo →
  ∀ index →
  BishopReal._≤_
    (Recurrence.sineMagnitudeTerm value (suc index))
    (Recurrence.sineMagnitudeTerm value index)
sineMagnitudeDecreasingTwoBall value insideTwo index =
  let
    magnitude = Recurrence.sineMagnitudeTerm value index
    successorToRatio =
      Factorial.sineSuccessorBelowCoarseRatio value index
    ratioToTwoThird =
      BishopProperties.*-monoʳ-≤-nonNeg
        (sineRatioBelowTwoThird value insideTwo)
        (Recurrence.sineMagnitudeTermNonnegative value index)
    twoThirdToOne =
      BishopProperties.*-monoʳ-≤-nonNeg
        bishopTwoThirdBelowOne
        (Recurrence.sineMagnitudeTermNonnegative value index)
  in
  BishopProperties.≤-trans successorToRatio
    (BishopProperties.≤-trans ratioToTwoThird
      (BishopProperties.≤-respʳ-≃
        (BishopProperties.*-identityˡ magnitude)
        twoThirdToOne))

record ConcreteTwoBallSineInputs
    (dataSet : Elementary.BishopElementaryPowerSeriesData)
    (value : BishopReal.ℝ) : Set₁ where
  field
    termIdentification :
      Terms.ConcreteSineCosineTermIdentification dataSet
    valueNonnegative : BishopReal.NonNegative value
    insideTwo : BishopReal._≤_ (BishopReal.∣_∣ value) bishopTwo

open ConcreteTwoBallSineInputs public

twoBallSineAlternatingSeriesData :
  ∀ {dataSet value} →
  ConcreteTwoBallSineInputs dataSet value →
  Alternating.AlternatingDecreasingSeriesData
twoBallSineAlternatingSeriesData {dataSet} {value} inputs = record
  { Alternating.AlternatingDecreasingSeriesData.term =
      Elementary.sineTerm dataSet value
  ; Alternating.AlternatingDecreasingSeriesData.magnitude =
      Recurrence.sineMagnitudeTerm value
  ; Alternating.AlternatingDecreasingSeriesData.representedLimit =
      Elementary.bishopSin dataSet value
  ; Alternating.AlternatingDecreasingSeriesData.magnitudeNonnegative =
      Recurrence.sineMagnitudeTermNonnegative value
  ; Alternating.AlternatingDecreasingSeriesData.magnitudeDecreasing =
      sineMagnitudeDecreasingTwoBall value (insideTwo inputs)
  ; Alternating.AlternatingDecreasingSeriesData.evenTermIsPositiveMagnitude =
      λ index →
        BishopProperties.≃-trans
          (Terms.sineTermIsConcrete
            (termIdentification inputs) value (Alternating.double index))
          (Concrete.sineSignedEvenIsMagnitude value
            (valueNonnegative inputs) index)
  ; Alternating.AlternatingDecreasingSeriesData.oddTermIsNegativeMagnitude =
      λ index →
        BishopProperties.≃-trans
          (Terms.sineTermIsConcrete
            (termIdentification inputs) value
            (suc (Alternating.double index)))
          (Concrete.sineSignedOddIsNegativeMagnitude value
            (valueNonnegative inputs) index)
  ; Alternating.AlternatingDecreasingSeriesData.seriesConvergesToRepresentedLimit =
      Elementary.bishopSinConvergence dataSet value
  }

twoBallSineInterlacing :
  ∀ {dataSet value} →
  ConcreteTwoBallSineInputs dataSet value →
  Interlacing.BishopAlternatingInterlacingData
twoBallSineInterlacing inputs =
  Alternating.alternatingInterlacingData
    (twoBallSineAlternatingSeriesData inputs)

sineCubicLowerTwoBall :
  ∀ {dataSet value} →
  ConcreteTwoBallSineInputs dataSet value →
  BishopReal._≤_
    (BishopReal._-_ value (Polynomial.sineCubicTerm value))
    (Elementary.bishopSin dataSet value)
sineCubicLowerTwoBall {value = value} inputs =
  let
    sineData = twoBallSineAlternatingSeriesData inputs
    raw = Interlacing.lowerPartialBelowRepresentedLimit
      (twoBallSineInterlacing inputs) (suc zero)

    lowerAsMagnitudes =
      Low.lowerOneEquivalentFirstMinusSecondMagnitude sineData

    firstAsValue =
      Polynomial.sineMagnitudeZeroEquivalentValue
        value (valueNonnegative inputs)

    secondAsCubic =
      Polynomial.sineMagnitudeOneEquivalentCubic
        value (valueNonnegative inputs)

    polynomialAsLower :
      BishopReal._≃_
        (BishopReal._-_ value (Polynomial.sineCubicTerm value))
        (Alternating.lowerPartial sineData (suc zero))
    polynomialAsLower =
      BishopProperties.≃-trans
        (BishopProperties.+-cong
          (BishopProperties.≃-symm firstAsValue)
          (BishopProperties.-‿cong
            (BishopProperties.≃-symm secondAsCubic)))
        (BishopProperties.≃-symm lowerAsMagnitudes)
  in
  BishopProperties.≤-respˡ-≃ polynomialAsLower raw

bishopSineTwoBallMagnitudeDecreaseLevel : ProofLevel
bishopSineTwoBallMagnitudeDecreaseLevel = machineChecked

bishopSineTwoBallCubicLowerLevel : ProofLevel
bishopSineTwoBallCubicLowerLevel = machineChecked
