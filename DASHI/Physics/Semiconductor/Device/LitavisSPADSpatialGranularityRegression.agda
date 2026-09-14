module DASHI.Physics.Semiconductor.Device.LitavisSPADSpatialGranularityRegression where

open import DASHI.Core.Prelude

import DASHI.Physics.Semiconductor.Device.LitavisSPADSpatialGranularityExact as Spatial

record LitavisSpatialGranularityRegression : Set₁ where
  constructor litavis-spatial-granularity-regression
  field
    macroTimingSurfaceDoesNotPayFineSpatialIdentity :
      Spatial.FineSpatialIdentityDefect
    joinedSpatialObserverPaysFineIdentity :
      Spatial.JoinedSpatialIdentityAdequacy
    sourceDimensionsRemainSeparateFromWiringInference :
      Spatial.SpatialGranularityBoundary

canonicalLitavisSpatialGranularityRegression :
  LitavisSpatialGranularityRegression
canonicalLitavisSpatialGranularityRegression =
  litavis-spatial-granularity-regression
    Spatial.fineSpatialIdentityDefect
    Spatial.joinedSpatialIdentityAdequate
    Spatial.canonicalSpatialGranularityBoundary
