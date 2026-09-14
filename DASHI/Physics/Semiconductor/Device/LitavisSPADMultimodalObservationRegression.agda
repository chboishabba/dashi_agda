module DASHI.Physics.Semiconductor.Device.LitavisSPADMultimodalObservationRegression where

open import DASHI.Core.Prelude

import DASHI.Physics.Semiconductor.Device.LitavisSPADMultimodalObservationExact as Litavis

record LitavisSPADRegression : Set₁ where
  constructor litavisSPADRegression
  field
    intensityProjectionPaysIntensityQuery :
      Litavis.IntensityAdequacy
    intensityProjectionDoesNotPayTimingQuery :
      Litavis.TimingDefect
    intensityProjectionDoesNotPayHistogramQuery :
      Litavis.HistogramDefect
    multimodalProjectionPaysTimingQuery :
      Litavis.MultimodalTimingAdequacy
    multimodalProjectionPaysHistogramQuery :
      Litavis.MultimodalHistogramAdequacy
    sourceClaimsRemainNonPromoting :
      Litavis.SourceClaimBoundary

canonicalLitavisSPADRegression : LitavisSPADRegression
canonicalLitavisSPADRegression =
  litavisSPADRegression
    Litavis.intensityQueryAdequate
    Litavis.timingQueryDefect
    Litavis.histogramQueryDefect
    Litavis.multimodalTimingQueryAdequate
    Litavis.multimodalHistogramQueryAdequate
    Litavis.canonicalSourceClaimBoundary
