module DASHI.Physics.Closure.NSWholeSpacePhysicalMajorantDominationProducerExact where

------------------------------------------------------------------------
-- WHOLE-SPACE A3 / ACTUAL ENVELOPES -> PHYSICAL MAJORANT DOMINATION
--
-- A1/A2 are the two analytic envelope integrability theorems.  This owner pays
-- the A3 same-object/record seam only: once the actual physical low/high
-- majorants are identified pointwise with those envelopes, the existing
-- domination compiler is inhabited without any extra analytic assumption.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import Real as BishopReal

import DASHI.Physics.Closure.NSTriadKNEuclideanSignedFrequencyCarrierRealizationExact as Euclidean
import DASHI.Physics.Closure.NSTriadKNEuclideanLebesgueSignedAggregationExact as Lebesgue
import DASHI.Physics.Closure.NSWholeSpacePhysicalMajorantDominationExact as Dom

record PhysicalEnvelopeInputs
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

    PointwiseBelow :
      (Euclidean.EuclideanInteraction → BishopReal.ℝ) →
      (Euclidean.EuclideanInteraction → BishopReal.ℝ) → Set

    lowDominated :
      PointwiseBelow lowPhysicalMajorant lowConvolutionEnvelope

    highDominated :
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

open PhysicalEnvelopeInputs public

physicalMajorantDomination :
  ∀ {dataSet base} →
  PhysicalEnvelopeInputs {dataSet} base →
  Dom.PhysicalMajorantDomination {dataSet} base
physicalMajorantDomination I = record
  { Dom.lowPhysicalMajorant = lowPhysicalMajorant I
  ; Dom.highPhysicalMajorant = highPhysicalMajorant I
  ; Dom.lowConvolutionEnvelope = lowConvolutionEnvelope I
  ; Dom.highWeightedConvolutionEnvelope = highWeightedConvolutionEnvelope I
  ; Dom.PointwiseBelow = PointwiseBelow I
  ; Dom.lowPhysicalBelowConvolution = lowDominated I
  ; Dom.highPhysicalBelowWeightedConvolution = highDominated I
  ; Dom.lowConvolutionEnvelopeIntegrable =
      lowConvolutionEnvelopeIntegrable I
  ; Dom.highWeightedConvolutionEnvelopeIntegrable =
      highWeightedConvolutionEnvelopeIntegrable I
  ; Dom.integrableOfDomination = integrableOfDomination I
  }

physicalMajorantDominationProducerCompilerClosed : Bool
physicalMajorantDominationProducerCompilerClosed = true

lowEnvelopeAnalyticProducerInhabitedHere : Bool
lowEnvelopeAnalyticProducerInhabitedHere = false

highEnvelopeAnalyticProducerInhabitedHere : Bool
highEnvelopeAnalyticProducerInhabitedHere = false

physicalMajorantDominationProducerIntroducesPostulate : Bool
physicalMajorantDominationProducerIntroducesPostulate = false

clayPromotion : Bool
clayPromotion = false

physicalMajorantDominationProducerCompilerClosedIsTrue :
  physicalMajorantDominationProducerCompilerClosed ≡ true
physicalMajorantDominationProducerCompilerClosedIsTrue = refl
