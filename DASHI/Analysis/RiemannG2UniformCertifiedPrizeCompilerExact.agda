module DASHI.Analysis.RiemannG2UniformCertifiedPrizeCompilerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Primitive using (Set₂)

import DASHI.Analysis.RiemannAnalyticSubstrate as Analytic
import DASHI.Analysis.RiemannAristotleUniversalEvenConeBidiExact as Universal
import DASHI.Analysis.RiemannG2UniformCertifiedHighOffLineProducerExact as Uniform

------------------------------------------------------------------------
-- UNIFORM CERTIFIED HIGH PRODUCER + LOW CERTIFICATE -> PRIZE-FACING RH
--
-- This is the final dependency compiler for the concrete preferred route.
-- The high theorem is not one finite certificate: it is the uniform family
-- already isolated by UniformCertifiedHighOffLineProducerExact.  Low criticality
-- remains independently certified on the same analytic zero carrier.
------------------------------------------------------------------------

record UniformCertifiedPrizePacket : Set₂ where
  field
    analytic : Analytic.AnalyticSubstrate
    Low High : Universal.AnalyticNontrivialZero analytic → Set

    coverLowHigh :
      (ρ : Universal.AnalyticNontrivialZero analytic) →
      Low ρ ⊎ High ρ

    lowCertifiedCritical :
      (ρ : Universal.AnalyticNontrivialZero analytic) →
      Low ρ →
      Universal.analyticCritical ρ

    criticalLineStable : Universal.CriticalLineStable analytic

    uniformHighProducer :
      Uniform.UniformCertifiedHighOffLineProducer analytic High

open UniformCertifiedPrizePacket public

compileUniformCertifiedPrizeRH :
  (packet : UniformCertifiedPrizePacket) →
  Analytic.RiemannHypothesisFor (analytic packet)
compileUniformCertifiedPrizeRH packet =
  Universal.analyticCoreHighLowCompletionImpliesRH
    (analytic packet)
    (Low packet)
    (High packet)
    (coverLowHigh packet)
    (lowCertifiedCritical packet)
    (criticalLineStable packet)
    (Uniform.compileUniformCertifiedHighOffLineProducer
      (uniformHighProducer packet))

------------------------------------------------------------------------
-- Search cut.
------------------------------------------------------------------------

record UniformCertifiedPrizeBoundary : Set where
  constructor uniform-certified-prize-boundary
  field
    oneFixedHighCertificateSufficesForPrize : Bool
    oneFixedHighCertificateSufficesForPrizeIsFalse :
      oneFixedHighCertificateSufficesForPrize ≡ false

    uniformHighProducerPlusLowCertificateCompilesRH : Bool
    uniformHighProducerPlusLowCertificateCompilesRHIsTrue :
      uniformHighProducerPlusLowCertificateCompilesRH ≡ true

    lowCertificateManufacturedByHighCompiler : Bool
    lowCertificateManufacturedByHighCompilerIsFalse :
      lowCertificateManufacturedByHighCompiler ≡ false

    finalExtraRHTheoremRequiredAfterPacket : Bool
    finalExtraRHTheoremRequiredAfterPacketIsFalse :
      finalExtraRHTheoremRequiredAfterPacket ≡ false

    prizePacketInhabitedHere : Bool
    prizePacketInhabitedHereIsFalse :
      prizePacketInhabitedHere ≡ false

canonicalUniformCertifiedPrizeBoundary : UniformCertifiedPrizeBoundary
canonicalUniformCertifiedPrizeBoundary =
  uniform-certified-prize-boundary
    false refl
    true refl
    false refl
    false refl
    false refl
