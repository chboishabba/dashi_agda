module DASHI.Physics.Semiconductor.Device.LitavisSPADConsumerSafeReductionRegression where

open import DASHI.Core.Prelude

import DASHI.Physics.Semiconductor.Device.LitavisSPADConsumerSafeReductionExact as Reduction

record LitavisConsumerSafeReductionRegression : Set₁ where
  constructor litavis-consumer-safe-reduction-regression
  field
    histogramReductionPaysHistogramConsumer :
      Reduction.HistogramReductionAdequacy
    histogramReductionDoesNotPayExactTimestampConsumer :
      Reduction.ExactTimestampReductionDefect
    joinedReductionPaysBothDeclaredConsumers :
      Reduction.JoinedReductionAdequacy
    sourceSnowballCountIsFour :
      Reduction.reductionSourceCount ≡ 4
    sourceSnowballRetainsBoundaries :
      Reduction.ReductionSourceBoundary
    reductionSafetyRemainsConsumerRelative :
      Reduction.ReductionSafetyBoundary

canonicalLitavisConsumerSafeReductionRegression :
  LitavisConsumerSafeReductionRegression
canonicalLitavisConsumerSafeReductionRegression =
  litavis-consumer-safe-reduction-regression
    Reduction.histogramReductionAdequate
    Reduction.exactTimestampReductionDefect
    Reduction.joinedReductionAdequate
    Reduction.reductionSourceCountIsFour
    Reduction.canonicalReductionSourceBoundary
    Reduction.canonicalReductionSafetyBoundary
