module DASHI.Physics.Closure.NSWholeSpaceLowHighConvolutionProducerExact where

------------------------------------------------------------------------
-- WHOLE-SPACE A / EXACT LOW-HIGH CONVOLUTION PRODUCER INTERFACE
--
-- The compensated A integrand must be paid by two genuinely analytic
-- inequalities, not by integrating a naked resolvent singularity.
--
-- LOW:
--   after heat-cube cancellation, the physical integrand is dominated by a
--   compact-output convolution F(eta) G(xi-eta).
--
-- HIGH:
--   the same state-side quantity carries the genuine resolvent tail
--   |xi|^-6 and is dominated by an integrable weighted convolution.
--
-- This owner makes the two measure-theoretic statements exact and proves that
-- they feed the already-constructed low/high majorant compiler.  It does not
-- postulate either theorem as already proved.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import Real as BishopReal

import DASHI.Physics.Closure.NSTriadKNEuclideanSignedFrequencyCarrierRealizationExact as Euclidean
import DASHI.Physics.Closure.NSTriadKNEuclideanLebesgueSignedAggregationExact as Lebesgue
import DASHI.Physics.Closure.NSWholeSpaceCompensatedMajorantLowHighGlueExact as Glue

record WholeSpaceLowHighConvolutionProducer
    {dataSet : Euclidean.EuclideanSignedFluxData}
    (base : Lebesgue.EuclideanLebesgueIntegralAuthority dataSet) : Set₁ where
  field
    lowPhysicalMajorant :
      Euclidean.EuclideanInteraction → BishopReal.ℝ
    highPhysicalMajorant :
      Euclidean.EuclideanInteraction → BishopReal.ℝ

    LowConvolutionCurrency : Set
    HighConvolutionCurrency : Set

    lowCurrency : LowConvolutionCurrency
    highCurrency : HighConvolutionCurrency

    -- This is the actual compact-output Young/Cauchy theorem after
    -- low-frequency cancellation.
    lowConvolutionIntegrable :
      LowConvolutionCurrency →
      Lebesgue.Integrable base lowPhysicalMajorant

    -- This is the actual |xi|^-6 weighted convolution theorem at infinity.
    highWeightedConvolutionIntegrable :
      HighConvolutionCurrency →
      Lebesgue.Integrable base highPhysicalMajorant

open WholeSpaceLowHighConvolutionProducer public

lowPhysicalMajorantIntegrable :
  ∀ {dataSet base} →
  (P : WholeSpaceLowHighConvolutionProducer {dataSet} base) →
  Lebesgue.Integrable base (lowPhysicalMajorant P)
lowPhysicalMajorantIntegrable P =
  lowConvolutionIntegrable P (lowCurrency P)

highPhysicalMajorantIntegrable :
  ∀ {dataSet base} →
  (P : WholeSpaceLowHighConvolutionProducer {dataSet} base) →
  Lebesgue.Integrable base (highPhysicalMajorant P)
highPhysicalMajorantIntegrable P =
  highWeightedConvolutionIntegrable P (highCurrency P)

lowCompensatedConvolutionTargetIsolated : Bool
lowCompensatedConvolutionTargetIsolated = true

highInverseSixthConvolutionTargetIsolated : Bool
highInverseSixthConvolutionTargetIsolated = true

nativeR3YoungCauchyProducerClosedHere : Bool
nativeR3YoungCauchyProducerClosedHere = false

nativeInverseSixthTailProducerClosedHere : Bool
nativeInverseSixthTailProducerClosedHere = false

clayPromotion : Bool
clayPromotion = false

lowCompensatedConvolutionTargetIsolatedIsTrue :
  lowCompensatedConvolutionTargetIsolated ≡ true
lowCompensatedConvolutionTargetIsolatedIsTrue = refl
