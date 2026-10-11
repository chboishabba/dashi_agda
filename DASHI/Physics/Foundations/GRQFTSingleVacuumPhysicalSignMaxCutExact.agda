{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.GRQFTSingleVacuumPhysicalSignMaxCutExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
import Data.Integer.Base as Int
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _/_; _*_; _-_; _<_; Positive; positive)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as Ring
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Foundations.GRQFTSingleVacuumNormalizationScaleCovarianceExact as Scale
import DASHI.Physics.Foundations.GRQFTVacuumAmplitudeDifferentialRenormalizationExact as Differential

------------------------------------------------------------------------
-- PHYSICAL SIGN / CONTROL MAX-CUT
------------------------------------------------------------------------

calibrationSquarePositive : ∀ k → 0ℚ < k → 0ℚ < k * k
calibrationSquarePositive k kPositive =
  let
    instance
      kPositiveInstance : Positive k
      kPositiveInstance = positive kPositive

    scaled : k * 0ℚ < k * k
    scaled = ℚP.*-monoˡ-<-pos k kPositive
  in
  subst
    (λ left → left < k * k)
    (Ring.solve-∀ k)
    scaled

positiveSourcePromotesPositivePhysicalAmplitude :
  ∀ source k →
  0ℚ < source →
  0ℚ < k →
  0ℚ < Scale.rescaledVacuumAmplitude source k
positiveSourcePromotesPositivePhysicalAmplitude source k sourcePositive kPositive =
  let
    kSquared = k * k
    kSquaredPositive : 0ℚ < kSquared
    kSquaredPositive = calibrationSquarePositive k kPositive

    instance
      kSquaredPositiveInstance : Positive kSquared
      kSquaredPositiveInstance = positive kSquaredPositive

    scaled : kSquared * 0ℚ < kSquared * source
    scaled = ℚP.*-monoˡ-<-pos kSquared sourcePositive
  in
  subst
    (λ left → left < Scale.rescaledVacuumAmplitude source k)
    (Ring.solve-∀ k)
    scaled

zeroSourcePromotesZeroPhysicalAmplitude :
  ∀ k → Scale.rescaledVacuumAmplitude 0ℚ k ≡ 0ℚ
zeroSourcePromotesZeroPhysicalAmplitude = Ring.solve-∀

positiveMultiplicativePreservesPositiveDifference :
  ∀ modulation →
  0ℚ < Differential.sourceOn modulation - Differential.sourceOff modulation →
  0ℚ < Differential.physicalVacuumDifference modulation
positiveMultiplicativePreservesPositiveDifference modulation sourceDifferencePositive =
  let
    m = Differential.multiplicative modulation
    sourceDifference =
      Differential.sourceOn modulation - Differential.sourceOff modulation

    instance
      mPositive : Positive m
      mPositive = positive (Differential.multiplicativePositive modulation)

    scaled : m * 0ℚ < m * sourceDifference
    scaled = ℚP.*-monoˡ-<-pos m sourceDifferencePositive

    productPositive : 0ℚ < m * sourceDifference
    productPositive =
      subst
        (λ left → left < m * sourceDifference)
        (Ring.solve-∀ m)
        scaled
  in
  subst
    (λ value → 0ℚ < value)
    (Relation.Binary.PropositionalEquality.sym
      (Differential.physicalVacuumDifferenceIsMultiplicativeSourceDifference modulation))
    productPositive

zeroSourceDifferenceGivesZeroPhysicalDifference :
  ∀ modulation →
  Differential.sourceOn modulation ≡ Differential.sourceOff modulation →
  Differential.physicalVacuumDifference modulation ≡ 0ℚ
zeroSourceDifferenceGivesZeroPhysicalDifference modulation sameSource
  rewrite Differential.physicalVacuumDifferenceIsMultiplicativeSourceDifference modulation
        | sameSource =
  Ring.solve-∀ (Differential.multiplicative modulation)
    (Differential.sourceOff modulation)

differentialMetricResponse : ℚ → Differential.CommonCountertermVacuumModulation → ℚ
differentialMetricResponse radius modulation =
  (radius * radius / (Int.+ 3 / 1))
  * Differential.physicalVacuumDifference modulation

zeroSourceDifferenceGivesZeroMetricModulation :
  ∀ radius modulation →
  Differential.sourceOn modulation ≡ Differential.sourceOff modulation →
  differentialMetricResponse radius modulation ≡ 0ℚ
zeroSourceDifferenceGivesZeroMetricModulation radius modulation sameSource
  rewrite zeroSourceDifferenceGivesZeroPhysicalDifference modulation sameSource =
  Ring.solve-∀ radius

record SingleVacuumPhysicalSignMaxCutBoundary : Set where
  constructor single-vacuum-physical-sign-max-cut-boundary
  field
    positiveSquareCalibrationPreservesPositiveSourceSign : Bool
    zeroStaticSourceRemainsZeroUnderMultiplicativeCalibration : Bool
    positiveDifferentialCalibrationPreservesPositiveSourceDifference : Bool
    zeroSourceDifferenceForcesZeroPhysicalDifference : Bool
    zeroSourceDifferenceForcesZeroScalarMetricModulation : Bool
    staticRouteNeedsPositivePromotedVacuumSign : Bool
    differentialRouteNeedsNonzeroSourceDifferenceForNonzeroSignal : Bool
    sourceSignOrControlCanBeRecoveredFromCouplingHistoryAlone : Bool

canonicalSingleVacuumPhysicalSignMaxCutBoundary :
  SingleVacuumPhysicalSignMaxCutBoundary
canonicalSingleVacuumPhysicalSignMaxCutBoundary =
  single-vacuum-physical-sign-max-cut-boundary
    true true true true true true true false

staticRouteNeedsPositivePromotedVacuumSign : Bool
staticRouteNeedsPositivePromotedVacuumSign = true

differentialRouteNeedsNonzeroSourceDifferenceForNonzeroSignal : Bool
differentialRouteNeedsNonzeroSourceDifferenceForNonzeroSignal = true
