module DASHI.Physics.Optics.CausticFreeformSourceAtlasExact where

open import DASHI.Core.Prelude

import DASHI.Physics.Foundations.PathIntegralExperimentalSourceRegistryExact as Sources

------------------------------------------------------------------------
-- SOURCE ATLAS: retain analysis/singularity authority separately from
-- inverse caustic/freeform design authority.
------------------------------------------------------------------------

berryUpstillCausticAnalysis : Sources.SourceReference
berryUpstillCausticAnalysis = Sources.berryUpstill1980

arnoldCausticSingularities : Sources.SourceReference
arnoldCausticSingularities = Sources.arnold1990Caustics

meyronMerigotThibert2018 : Sources.SourceReference
meyronMerigotThibert2018 = Sources.sourceReference
  "Jocelyn Meyron; Quentin Merigot; Boris Thibert"
  "Light in Power: A General and Parameter-free Algorithm for Caustic Design"
  "ACM Transactions on Graphics 37(6), Article 224"
  2018
  "10.1145/3272127.3275056"
  "inverse caustic design for reflective/refractive optical components under source-to-target light-energy constraints; does not imply every desired target is realised by every surface class or under wave-optical regimes"

zhouSunDengZhang2026 : Sources.SourceReference
zhouSunDengZhang2026 = Sources.sourceReference
  "Sizhuo Zhou; Yuou Sun; Bailin Deng; Juyong Zhang"
  "Computational Caustic Design for Surface Light Source"
  "IEEE Transactions on Visualization and Computer Graphics 32(2), 1911-1927"
  2026
  "10.1109/TVCG.2025.3633081"
  "freeform-lens caustic design using fitted surface-light-source models, flux consistency and normal integrability; supports real-source refinement rather than replacing source calibration with a point-source assumption"

record CausticFreeformSourceBoundary : Set where
  constructor caustic-freeform-source-boundary
  field
    analysisSourceDistinctFromDesignSource : Bool
    analysisSourceDistinctFromDesignSourceIsTrue :
      analysisSourceDistinctFromDesignSource ≡ true
    sourceModelIsExplicitCoordinate : Bool
    sourceModelIsExplicitCoordinateIsTrue : sourceModelIsExplicitCoordinate ≡ true
    sourceCitationAloneProvesDesign : Bool
    sourceCitationAloneProvesDesignIsFalse : sourceCitationAloneProvesDesign ≡ false

canonicalCausticFreeformSourceBoundary : CausticFreeformSourceBoundary
canonicalCausticFreeformSourceBoundary =
  caustic-freeform-source-boundary true refl true refl false refl
