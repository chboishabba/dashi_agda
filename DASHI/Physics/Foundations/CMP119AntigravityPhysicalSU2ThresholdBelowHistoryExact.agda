{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityPhysicalSU2ThresholdBelowHistoryExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; 1ℚ; _*_; _≤_; _<_)
import Data.Rational.Properties as ℚP
open import Relation.Nullary.Decidable using (toWitness)

import Real as Bishop
import RealProperties as BishopP

import DASHI.Physics.Foundations.CMP119AntigravityBishopInversePiSquaredUnitBoundExact as Pi
import DASHI.Physics.YangMills.BalabanClayT4BishopFourCornerIntervalExact as Embed
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- PHYSICAL SU(2) TRACE-ENERGY THRESHOLD IN THE BISHOP REAL CARRIER
--
--   threshold_phys = (11/24) * pi^{-2}.
--
-- From pi^{-2} <= 1 and 11/24 < 1:
--
--   threshold_phys <= 1.
--
-- Therefore every rational history inverse threshold with 1 <= u_* dominates
-- the physical anomaly threshold after the standard rational->Bishop embedding.
------------------------------------------------------------------------

elevenTwentyFour : ℚ
elevenTwentyFour = + 11 / 24

elevenTwentyFourNonnegative : 0ℚ ≤ elevenTwentyFour
elevenTwentyFourNonnegative =
  ℚP.<⇒≤ (ℚP.positive⁻¹ elevenTwentyFour)

elevenTwentyFourAtMostOne : elevenTwentyFour ≤ 1ℚ
elevenTwentyFourAtMostOne =
  toWitness {a? = elevenTwentyFour ℚP.≤? 1ℚ} _

embeddedCoefficient : Bishop.ℝ
embeddedCoefficient = Embed.embed elevenTwentyFour

embeddedCoefficientNonnegative :
  Bishop.NonNegative embeddedCoefficient
embeddedCoefficientNonnegative =
  BishopP.0≤x⇒nonNegx
    (BishopP.≤-respˡ-≃
      Embed.embedZero
      (Embed.embedOrder elevenTwentyFourNonnegative))

embeddedCoefficientAtMostOne :
  Bishop._≤_ embeddedCoefficient Bishop.1ℝ
embeddedCoefficientAtMostOne =
  BishopP.≤-respʳ-≃
    Embed.embedOne
    (Embed.embedOrder elevenTwentyFourAtMostOne)

inversePiSquaredNonnegative :
  Bishop.NonNegative Pi.inversePiSquared
inversePiSquaredNonnegative =
  BishopP.nonNegx,y⇒nonNegx*y
    (BishopP.pos⇒nonNeg (BishopP.0<x⇒posx Pi.inversePiPositive))
    (BishopP.pos⇒nonNeg (BishopP.0<x⇒posx Pi.inversePiPositive))

physicalSU2NoGoThreshold : Bishop.ℝ
physicalSU2NoGoThreshold =
  Bishop._*_ embeddedCoefficient Pi.inversePiSquared

physicalSU2NoGoThresholdAtMostOne :
  Bishop._≤_ physicalSU2NoGoThreshold Bishop.1ℝ
physicalSU2NoGoThresholdAtMostOne =
  let
    productBound :
      Bishop._≤_
        (Bishop._*_ embeddedCoefficient Pi.inversePiSquared)
        (Bishop._*_ Bishop.1ℝ Bishop.1ℝ)
    productBound =
      BishopP.*-mono-≤
        embeddedCoefficientNonnegative
        inversePiSquaredNonnegative
        embeddedCoefficientAtMostOne
        (BishopP.≤-respʳ-≃
          Embed.embedOne
          Pi.inversePiSquaredAtMostOne)
  in
  BishopP.≤-respʳ-≃
    (BishopP.*-identityˡ Bishop.1ℝ)
    productBound

historyAtLeastOneDominatesPhysicalSU2Threshold :
  ∀ {inverseThreshold : ℚ} →
  1ℚ ≤ inverseThreshold →
  Bishop._≤_
    physicalSU2NoGoThreshold
    (Embed.embed inverseThreshold)
historyAtLeastOneDominatesPhysicalSU2Threshold oneBelow =
  BishopP.≤-trans
    physicalSU2NoGoThresholdAtMostOne
    (BishopP.≤-respˡ-≃
      (BishopP.≃-symm Embed.embedOne)
      (Embed.embedOrder oneBelow))

physicalSU2ThresholdNumericComparisonClosed : Bool
physicalSU2ThresholdNumericComparisonClosed = true

selectedAnomalyInversePiSquaredSameMachinConventionStillRequired : Bool
selectedAnomalyInversePiSquaredSameMachinConventionStillRequired = true

physicalSU2ThresholdNumericComparisonClosedIsTrue :
  physicalSU2ThresholdNumericComparisonClosed ≡ true
physicalSU2ThresholdNumericComparisonClosedIsTrue = refl

selectedAnomalyInversePiSquaredSameMachinConventionStillRequiredIsTrue :
  selectedAnomalyInversePiSquaredSameMachinConventionStillRequired ≡ true
selectedAnomalyInversePiSquaredSameMachinConventionStillRequiredIsTrue = refl

physicalSU2ThresholdBelowHistoryCompilerLevel : ProofLevel
physicalSU2ThresholdBelowHistoryCompilerLevel = machineChecked
