module DASHI.Physics.YangMills.BalabanBishopFactorialPowerRecurrenceExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Zachary Murray,
-- "Constructive Analysis in the Agda Proof Assistant",
-- B.Sc. Honours thesis, Dalhousie University, 2022.
-- arXiv:2205.08354. No DOI assigned.
--
-- Code continuation: Viktor Csimma, viktorcsimma/bishop, pinned by DASHI at
-- vendor/bishop commit 240e38c7f6938f20f865b1f956c5f084da48bd54.
--
-- PURPOSE
-- Close the exponent/power half of the concrete sine and cosine recurrence.
-- The only remaining arithmetic leaf is the factorial-denominator comparison
-- showing that the exact successor term is below the coarse |x|^2/6 or
-- |x|^2/2 multiple of the current term.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Nat.Base using (NonZero)
open import Data.Nat.Properties using (_!≢0)
open import Data.Integer.Base using (+_; nonNeg)
open import Data.Rational.Unnormalised as ℚ using (0ℚᵘ; _/_)
import Data.Rational.Unnormalised.Properties as ℚP

import Real as BishopReal
import RealProperties as BishopProperties

import DASHI.Physics.YangMills.BalabanClayGate4BishopHalfRadiusRealEstimatesExact as Estimates
import DASHI.Physics.YangMills.BalabanBishopConcreteHalfBallSquareExact as HalfBall
import DASHI.Physics.YangMills.BalabanBishopConcreteHalfRadiusRatiosExact as Ratios
open import DASHI.Physics.YangMills.CompactLieProofLevel

powTwoStep :
  (value : BishopReal.ℝ) (index : Nat) →
  BishopReal._≃_
    (BishopReal.pow value (suc (suc index)))
    (BishopReal._*_
      (BishopReal.pow value index)
      (BishopReal._*_ value value))
powTwoStep value index =
  BishopProperties.*-assoc
    (BishopReal.pow value index) value value

absPowTwoStep :
  (value : BishopReal.ℝ) (index : Nat) →
  BishopReal._≃_
    (BishopReal.∣_∣
      (BishopReal.pow value (suc (suc index))))
    (BishopReal._*_
      (BishopReal.∣_∣ (BishopReal.pow value index))
      (BishopReal._*_
        (BishopReal.∣_∣ value)
        (BishopReal.∣_∣ value)))
absPowTwoStep value index =
  BishopProperties.≃-trans
    (BishopProperties.∣-∣-cong (powTwoStep value index))
    (BishopProperties.≃-trans
      (BishopProperties.∣x*y∣≃∣x∣*∣y∣
        (BishopReal.pow value index)
        (BishopReal._*_ value value))
      (BishopProperties.*-congˡ
        (BishopProperties.∣x*y∣≃∣x∣*∣y∣ value value)))

absPowOddSuccessorSplit :
  (value : BishopReal.ℝ) (index : Nat) →
  BishopReal._≃_
    (BishopReal.∣_∣
      (BishopReal.pow value
        (Estimates.oddExponent (suc index))))
    (BishopReal._*_
      (BishopReal.∣_∣
        (BishopReal.pow value (Estimates.oddExponent index)))
      (BishopReal._*_
        (BishopReal.∣_∣ value)
        (BishopReal.∣_∣ value)))
absPowOddSuccessorSplit value index =
  absPowTwoStep value (Estimates.oddExponent index)

absPowEvenSuccessorSplit :
  (value : BishopReal.ℝ) (index : Nat) →
  BishopReal._≃_
    (BishopReal.∣_∣
      (BishopReal.pow value
        (Estimates.evenExponent (suc index))))
    (BishopReal._*_
      (BishopReal.∣_∣
        (BishopReal.pow value (Estimates.evenExponent index)))
      (BishopReal._*_
        (BishopReal.∣_∣ value)
        (BishopReal.∣_∣ value)))
absPowEvenSuccessorSplit value index =
  absPowTwoStep value (Estimates.evenExponent index)

sineMagnitudeTerm : BishopReal.ℝ → Nat → BishopReal.ℝ
sineMagnitudeTerm value index =
  BishopReal._*_
    (BishopReal._⋆
      (Estimates.inverseFactorialRational
        (Estimates.oddExponent index)))
    (BishopReal.∣_∣
      (BishopReal.pow value (Estimates.oddExponent index)))

cosineMagnitudeTerm : BishopReal.ℝ → Nat → BishopReal.ℝ
cosineMagnitudeTerm value index =
  BishopReal._*_
    (BishopReal._⋆
      (Estimates.inverseFactorialRational
        (Estimates.evenExponent index)))
    (BishopReal.∣_∣
      (BishopReal.pow value (Estimates.evenExponent index)))

factorialNonnegative : ∀ (w : Nat) .{{_ : NonZero w}} → ℚ.NonNegative (+ 1 / w)
factorialNonnegative (suc k) = nonNeg

inverseFactorialNonnegative : ∀ n → ℚ.NonNegative (Estimates.inverseFactorialRational n)
inverseFactorialNonnegative n =
  let instance _ = _!≢0 n in
  factorialNonnegative (Estimates.factorial n)

embeddedInverseFactorialNonnegative :
  ∀ index →
  BishopReal.NonNegative
    (BishopReal._⋆ (Estimates.inverseFactorialRational index))
embeddedInverseFactorialNonnegative index =
  BishopProperties.0≤x⇒nonNegx
    (BishopProperties.p≤q⇒p⋆≤q⋆
      0ℚᵘ
      (Estimates.inverseFactorialRational index)
      (ℚP.nonNegative⁻¹
        (Estimates.inverseFactorialRational index)
        ⦃ inverseFactorialNonnegative index ⦄))

sineMagnitudeTermNonnegative :
  ∀ value index →
  BishopReal.NonNegative (sineMagnitudeTerm value index)
sineMagnitudeTermNonnegative value index =
  BishopProperties.nonNegx,y⇒nonNegx*y
    (embeddedInverseFactorialNonnegative
      (Estimates.oddExponent index))
    (BishopProperties.nonNeg∣x∣
      (BishopReal.pow value (Estimates.oddExponent index)))

cosineMagnitudeTermNonnegative :
  ∀ value index →
  BishopReal.NonNegative (cosineMagnitudeTerm value index)
cosineMagnitudeTermNonnegative value index =
  BishopProperties.nonNegx,y⇒nonNegx*y
    (embeddedInverseFactorialNonnegative
      (Estimates.evenExponent index))
    (BishopProperties.nonNeg∣x∣
      (BishopReal.pow value (Estimates.evenExponent index)))

record ConcreteFactorialCoefficientStepBounds : Set₁ where
  field
    sineSuccessorBelowCoarseRatio :
      ∀ value index →
      BishopReal._≤_
        (sineMagnitudeTerm value (suc index))
        (BishopReal._*_
          (Ratios.bishopSineSuccessiveMagnitudeRatio value)
          (sineMagnitudeTerm value index))

    cosineSuccessorBelowCoarseRatio :
      ∀ value index →
      BishopReal._≤_
        (cosineMagnitudeTerm value (suc index))
        (BishopReal._*_
          (Ratios.bishopCosineSuccessiveMagnitudeRatio value)
          (cosineMagnitudeTerm value index))

open ConcreteFactorialCoefficientStepBounds public

sineMagnitudeTermRecurrence :
  ConcreteFactorialCoefficientStepBounds →
  ∀ value index →
  BishopReal._≤_ (BishopReal.∣_∣ value) HalfBall.bishopHalf →
  BishopReal._≤_
    (sineMagnitudeTerm value (suc index))
    (BishopReal._*_
      Ratios.bishopOneTwentyFourth
      (sineMagnitudeTerm value index))
sineMagnitudeTermRecurrence inputs value index insideHalf =
  BishopProperties.≤-trans
    (sineSuccessorBelowCoarseRatio inputs value index)
    (BishopProperties.*-monoʳ-≤-nonNeg
      (Ratios.bishopSineRatioBelowTwentyFourth value insideHalf)
      (sineMagnitudeTermNonnegative value index))

cosineMagnitudeTermRecurrence :
  ConcreteFactorialCoefficientStepBounds →
  ∀ value index →
  BishopReal._≤_ (BishopReal.∣_∣ value) HalfBall.bishopHalf →
  BishopReal._≤_
    (cosineMagnitudeTerm value (suc index))
    (BishopReal._*_
      Ratios.bishopOneEighth
      (cosineMagnitudeTerm value index))
cosineMagnitudeTermRecurrence inputs value index insideHalf =
  BishopProperties.≤-trans
    (cosineSuccessorBelowCoarseRatio inputs value index)
    (BishopProperties.*-monoʳ-≤-nonNeg
      (Ratios.bishopCosineRatioBelowEighth value insideHalf)
      (cosineMagnitudeTermNonnegative value index))

bishopPowerTwoStepLevel : ProofLevel
bishopPowerTwoStepLevel = machineChecked

bishopAbsolutePowerSuccessorSplitLevel : ProofLevel
bishopAbsolutePowerSuccessorSplitLevel = machineChecked

bishopCoefficientRecurrenceReducerLevel : ProofLevel
bishopCoefficientRecurrenceReducerLevel = machineChecked

bishopFactorialCoefficientStepLevel : ProofLevel
bishopFactorialCoefficientStepLevel = conditional
