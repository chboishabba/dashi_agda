module DASHI.Physics.YangMills.BalabanBishopConcreteHalfRadiusRatiosExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Zachary Murray, "Constructive Analysis in the Agda Proof Assistant",
-- B.Sc. Honours thesis, Dalhousie University, 2022.
-- arXiv:2205.08354. No DOI assigned.
--
-- Code continuation: Viktor Csimma, viktorcsimma/bishop, pinned by DASHI at
-- vendor/bishop commit 240e38c7f6938f20f865b1f956c5f084da48bd54.
--
-- PURPOSE
--
-- Instantiate the exact half-radius coefficient-ratio targets on Bishop reals:
--
--   |x| <= 1/2  ->  |x|^2 / 6 <= 1/24,
--   |x| <= 1/2  ->  |x|^2 / 2 <= 1/8.
--
-- This consumes the concrete square estimate rather than reintroducing the
-- quarter bound as a field.
------------------------------------------------------------------------

open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised as ℚ using
  (ℚᵘ; _/_; 0ℚᵘ)
import Data.Rational.Unnormalised.Properties as ℚP

import Real as BishopReal
import RealProperties as BishopProperties

import DASHI.Physics.YangMills.BalabanBishopConcreteHalfBallSquareExact as HalfBall
open import DASHI.Physics.YangMills.CompactLieProofLevel

oneSixth oneHalf oneTwentyFourth oneEighth : ℚᵘ
oneSixth = + 1 / 6
oneHalf = + 1 / 2
oneTwentyFourth = + 1 / 24
oneEighth = + 1 / 8

bishopOneSixth bishopOneHalf bishopOneTwentyFourth bishopOneEighth :
  BishopReal.ℝ
bishopOneSixth = BishopReal._⋆ oneSixth
bishopOneHalf = BishopReal._⋆ oneHalf
bishopOneTwentyFourth = BishopReal._⋆ oneTwentyFourth
bishopOneEighth = BishopReal._⋆ oneEighth

bishopOneSixthNonnegative :
  BishopReal.NonNegative bishopOneSixth
bishopOneSixthNonnegative =
  BishopProperties.0≤x⇒nonNegx
    (BishopProperties.p≤q⇒p⋆≤q⋆
      0ℚᵘ oneSixth (ℚP.nonNegative⁻¹ oneSixth))

bishopOneHalfNonnegative :
  BishopReal.NonNegative bishopOneHalf
bishopOneHalfNonnegative =
  BishopProperties.0≤x⇒nonNegx
    (BishopProperties.p≤q⇒p⋆≤q⋆
      0ℚᵘ oneHalf (ℚP.nonNegative⁻¹ oneHalf))

bishopQuarterTimesSixthEquivalentTwentyFourth :
  BishopReal._≃_
    (BishopReal._*_
      HalfBall.bishopQuarter
      bishopOneSixth)
    bishopOneTwentyFourth
bishopQuarterTimesSixthEquivalentTwentyFourth =
  BishopProperties.≃-trans
    (BishopProperties.≃-symm
      (BishopProperties.⋆-distrib-* HalfBall.quarter oneSixth))
    (BishopProperties.⋆-cong ℚP.≃-refl)

bishopQuarterTimesHalfEquivalentEighth :
  BishopReal._≃_
    (BishopReal._*_
      HalfBall.bishopQuarter
      bishopOneHalf)
    bishopOneEighth
bishopQuarterTimesHalfEquivalentEighth =
  BishopProperties.≃-trans
    (BishopProperties.≃-symm
      (BishopProperties.⋆-distrib-* HalfBall.quarter oneHalf))
    (BishopProperties.⋆-cong ℚP.≃-refl)

bishopSineSuccessiveMagnitudeRatio :
  BishopReal.ℝ → BishopReal.ℝ
bishopSineSuccessiveMagnitudeRatio value =
  BishopReal._*_
    (HalfBall.bishopMagnitudeSquare value)
    bishopOneSixth

bishopCosineSuccessiveMagnitudeRatio :
  BishopReal.ℝ → BishopReal.ℝ
bishopCosineSuccessiveMagnitudeRatio value =
  BishopReal._*_
    (HalfBall.bishopMagnitudeSquare value)
    bishopOneHalf

bishopSineRatioBelowTwentyFourth :
  (value : BishopReal.ℝ) →
  BishopReal._≤_ (BishopReal.∣_∣ value) HalfBall.bishopHalf →
  BishopReal._≤_
    (bishopSineSuccessiveMagnitudeRatio value)
    bishopOneTwentyFourth
bishopSineRatioBelowTwentyFourth value insideHalf =
  let squareBelowQuarter =
        HalfBall.bishopHalfBallMagnitudeSquareBelowQuarter value insideHalf
      multipliedBound =
        BishopProperties.*-monoʳ-≤-nonNeg
          squareBelowQuarter
          bishopOneSixthNonnegative
  in BishopProperties.≤-respʳ-≃
       bishopQuarterTimesSixthEquivalentTwentyFourth
       multipliedBound

bishopCosineRatioBelowEighth :
  (value : BishopReal.ℝ) →
  BishopReal._≤_ (BishopReal.∣_∣ value) HalfBall.bishopHalf →
  BishopReal._≤_
    (bishopCosineSuccessiveMagnitudeRatio value)
    bishopOneEighth
bishopCosineRatioBelowEighth value insideHalf =
  let squareBelowQuarter =
        HalfBall.bishopHalfBallMagnitudeSquareBelowQuarter value insideHalf
      multipliedBound =
        BishopProperties.*-monoʳ-≤-nonNeg
          squareBelowQuarter
          bishopOneHalfNonnegative
  in BishopProperties.≤-respʳ-≃
       bishopQuarterTimesHalfEquivalentEighth
       multipliedBound

record ConcreteBishopHalfRadiusRatioCertificate
    (value : BishopReal.ℝ) : Set where
  field
    insideHalf :
      BishopReal._≤_ (BishopReal.∣_∣ value) HalfBall.bishopHalf

    sineRatioBelowTwentyFourth :
      BishopReal._≤_
        (bishopSineSuccessiveMagnitudeRatio value)
        bishopOneTwentyFourth

    cosineRatioBelowEighth :
      BishopReal._≤_
        (bishopCosineSuccessiveMagnitudeRatio value)
        bishopOneEighth

open ConcreteBishopHalfRadiusRatioCertificate public

concreteBishopHalfRadiusRatioCertificate :
  (value : BishopReal.ℝ) →
  BishopReal._≤_ (BishopReal.∣_∣ value) HalfBall.bishopHalf →
  ConcreteBishopHalfRadiusRatioCertificate value
concreteBishopHalfRadiusRatioCertificate value inside = record
  { insideHalf = inside
  ; sineRatioBelowTwentyFourth =
      bishopSineRatioBelowTwentyFourth value inside
  ; cosineRatioBelowEighth =
      bishopCosineRatioBelowEighth value inside
  }

bishopConcreteHalfRadiusRatioLevel : ProofLevel
bishopConcreteHalfRadiusRatioLevel = machineChecked
