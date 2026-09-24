module DASHI.Physics.Closure.NSWholeSpacePhysicalMajorantDominationExact where

------------------------------------------------------------------------
-- WHOLE-SPACE A / PHYSICAL LOW-HIGH MAJORANT DOMINATION
--
-- The previous producer interface asked directly for integrability of the
-- physical low/high majorants.  This module moves the analytic boundary down:
--
--   low physical majorant  <= compact-output convolution envelope
--   high physical majorant <= inverse-sixth weighted convolution envelope
--
-- plus an integrability-preserving domination rule for the actual Lebesgue
-- authority.  Thus the naked resolvent singularity never appears as an
-- integrability hypothesis.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import Real as BishopReal

import DASHI.Physics.Closure.NSTriadKNEuclideanSignedFrequencyCarrierRealizationExact as Euclidean
import DASHI.Physics.Closure.NSTriadKNEuclideanLebesgueSignedAggregationExact as Lebesgue
import DASHI.Physics.Closure.NSWholeSpaceLowHighConvolutionProducerExact as Producer

record PhysicalMajorantDomination
    {dataSet : Euclidean.EuclideanSignedFluxData}
    (base : Lebesgue.EuclideanLebesgueIntegralAuthority dataSet) : Set₁ where
  field
    lowPhysicalMajorant :
      Euclidean.EuclideanInteraction → BishopReal.ℝ
    highPhysicalMajorant :
      Euclidean.EuclideanInteraction → BishopReal.ℝ

    lowConvolutionEnvelope :
      Euclidean.EuclideanInteraction → BishopReal.ℝ
    highWeightedConvolutionEnvelope :
      Euclidean.EuclideanInteraction → BishopReal.ℝ

    PointwiseBelow : (Euclidean.EuclideanInteraction → BishopReal.ℝ) →
                     (Euclidean.EuclideanInteraction → BishopReal.ℝ) → Set

    lowPhysicalBelowConvolution :
      PointwiseBelow lowPhysicalMajorant lowConvolutionEnvelope

    highPhysicalBelowWeightedConvolution :
      PointwiseBelow highPhysicalMajorant highWeightedConvolutionEnvelope

    lowConvolutionEnvelopeIntegrable :
      Lebesgue.Integrable base lowConvolutionEnvelope

    highWeightedConvolutionEnvelopeIntegrable :
      Lebesgue.Integrable base highWeightedConvolutionEnvelope

    integrableOfDomination :
      (f g : Euclidean.EuclideanInteraction → BishopReal.ℝ) →
      PointwiseBelow f g →
      Lebesgue.Integrable base g →
      Lebesgue.Integrable base f

open PhysicalMajorantDomination public

lowPhysicalIntegrableFromConvolution :
  ∀ {dataSet base} →
  (P : PhysicalMajorantDomination {dataSet} base) →
  Lebesgue.Integrable base (lowPhysicalMajorant P)
lowPhysicalIntegrableFromConvolution P =
  integrableOfDomination P
    (lowPhysicalMajorant P)
    (lowConvolutionEnvelope P)
    (lowPhysicalBelowConvolution P)
    (lowConvolutionEnvelopeIntegrable P)

highPhysicalIntegrableFromWeightedConvolution :
  ∀ {dataSet base} →
  (P : PhysicalMajorantDomination {dataSet} base) →
  Lebesgue.Integrable base (highPhysicalMajorant P)
highPhysicalIntegrableFromWeightedConvolution P =
  integrableOfDomination P
    (highPhysicalMajorant P)
    (highWeightedConvolutionEnvelope P)
    (highPhysicalBelowWeightedConvolution P)
    (highWeightedConvolutionEnvelopeIntegrable P)

dominationToLowHighProducer :
  ∀ {dataSet base} →
  PhysicalMajorantDomination {dataSet} base →
  Producer.WholeSpaceLowHighConvolutionProducer {dataSet} base
dominationToLowHighProducer P = record
  { Producer.lowPhysicalMajorant = lowPhysicalMajorant P
  ; Producer.highPhysicalMajorant = highPhysicalMajorant P
  ; Producer.LowConvolutionCurrency = Lebesgue.Integrable base (lowConvolutionEnvelope P)
  ; Producer.HighConvolutionCurrency = Lebesgue.Integrable base (highWeightedConvolutionEnvelope P)
  ; Producer.lowCurrency = lowConvolutionEnvelopeIntegrable P
  ; Producer.highCurrency = highWeightedConvolutionEnvelopeIntegrable P
  ; Producer.lowConvolutionIntegrable =
      λ _ → lowPhysicalIntegrableFromConvolution P
  ; Producer.highWeightedConvolutionIntegrable =
      λ _ → highPhysicalIntegrableFromWeightedConvolution P
  }

physicalMajorantIntegrabilityNoLongerOpaque : Bool
physicalMajorantIntegrabilityNoLongerOpaque = true

lowYoungCauchyEnvelopeStillAnalytic : Bool
lowYoungCauchyEnvelopeStillAnalytic = true

highInverseSixthEnvelopeStillAnalytic : Bool
highInverseSixthEnvelopeStillAnalytic = true

clayPromotion : Bool
clayPromotion = false

physicalMajorantIntegrabilityNoLongerOpaqueIsTrue :
  physicalMajorantIntegrabilityNoLongerOpaque ≡ true
physicalMajorantIntegrabilityNoLongerOpaqueIsTrue = refl
