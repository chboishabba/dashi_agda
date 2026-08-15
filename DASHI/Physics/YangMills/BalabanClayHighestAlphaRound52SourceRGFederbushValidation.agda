module DASHI.Physics.YangMills.BalabanClayHighestAlphaRound52SourceRGFederbushValidation where

------------------------------------------------------------------------
-- Focused Round-52 validation root.
--
-- This round combines the two shortest currently available routes:
--
-- G1 / source chart:
--   calibrated principal-log + centre-transport column bounds
--     -> local JT-I quarter bound
--     -> normalized contour-average quarter contraction
--     -> determinant-free 4/3 inverse bound.
--
-- RG1a/RG1b / complete density:
--   CMP109 rooted localization summability
--   + CMP119/CMP122 R-operation and boundary preservation
--   + CMP99 background propagator authority
--   + sufficiently-small coupling history
--     -> direct Sect.-2 complete-density -> canonical YM4 invariant-region state.
--
-- The remaining leaves are literal scalar/operator dictionaries and the
-- genuinely missing all-scale small-coupling history; no Clay promotion.
------------------------------------------------------------------------

import DASHI.Physics.YangMills.BalabanClayHighestAlphaRound51CentreKKTBetaValidation
import DASHI.Physics.YangMills.BalabanCMP109FederbushLogTransportToNormalizedInverseExact as Fed
import DASHI.Physics.YangMills.BalabanClayGate4LightweightValidation as Gate4
import DASHI.Physics.YangMills.Balaban1989CompleteDensityToYM4RegionExact as Complete
import DASHI.Physics.YangMills.Balaban1989CanonicalYM4StateFromSection2Exact as Canonical

federbushLogTransportToLocalResidualLevel =
  Fed.cmp109FederbushLogTransportToLocalResidualLevel

federbushLogTransportToNormalizedInverseLevel =
  Fed.cmp109FederbushLogTransportToNormalizedInverseLevel

federbushPhysicalLogTransportColumnBoundsLevel =
  Fed.physicalCMP109FederbushLogTransportColumnBoundsLevel

completeDensityToYM4RegionAssemblyLevel =
  Complete.balabanCompleteDensityToYM4RegionAssemblyLevel

canonicalYM4StateConstructionLevel =
  Canonical.balaban1989CanonicalYM4StateConstructionLevel

canonicalSection2ToYM4RegionLevel =
  Canonical.balaban1989CanonicalSection2ToYM4RegionLevel

section2ScalarCoordinateExtractionLevel =
  Canonical.balaban1989Section2ScalarCoordinateExtractionLevel

cmp109RootedLocalizationSummabilityLevel =
  Gate4.cmp109Equation026RootedSummabilityLevel

cmp109CMP122DirectRootedRAssemblyLevel =
  Gate4.cmp109CMP122DirectRootedRAssemblyLevel

balabanPhysicalSmallCouplingHistoryLevel =
  Gate4.balabanPhysicalSmallCouplingHistoryLevel
