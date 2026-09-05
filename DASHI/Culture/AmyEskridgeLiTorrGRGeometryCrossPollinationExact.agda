module DASHI.Culture.AmyEskridgeLiTorrGRGeometryCrossPollinationExact where

open import DASHI.Core.Prelude

import DASHI.Culture.AmyEskridgeLiTorrMagnitudeTriangleCrossPollinationExact as X
import DASHI.Physics.ExoticGravity.LiTorrStandardGRRotatingSourceKernelExact as GR
import DASHI.Physics.ExoticGravity.LiTorrGeometryAcquisitionBidiExact as GA

------------------------------------------------------------------------
-- ESKRIDGE x LI/TORR x STANDARD-GR GEOMETRY REFINEMENT
--
-- Cross-pollinates the generic weak-field rotating-source kernel back into the
-- Eskridge/Li-Torr magnitude programme without pretending the source papers
-- specify a unique literal apparatus.
------------------------------------------------------------------------

record GRGeometryCrossPollination : Set where
  constructor gr-geometry-cross-pollination
  field
    priorMagnitudeTriangleAvailable : Bool
    priorMagnitudeTriangleAvailableIsTrue :
      priorMagnitudeTriangleAvailable ≡ true

    weakFieldRotatingSourceKernelAvailable : Bool
    weakFieldRotatingSourceKernelAvailableIsTrue :
      weakFieldRotatingSourceKernelAvailable ≡ true

    exactHistoricalSourceGeometryAvailable : Bool
    exactHistoricalSourceGeometryAvailableIsFalse :
      exactHistoricalSourceGeometryAvailable ≡ false

    currentGeometryLeafIsSourceShape : Bool
    currentGeometryLeafIsSourceShapeIsTrue :
      currentGeometryLeafIsSourceShape ≡ true

canonicalGRGeometryCrossPollination : GRGeometryCrossPollination
canonicalGRGeometryCrossPollination =
  gr-geometry-cross-pollination true refl true refl false refl true refl

geometryFrontier : GA.GeometryLeaf
geometryFrontier = GA.currentFirstOpenGeometryLeaf

------------------------------------------------------------------------
-- Scientific interpretation boundary.
------------------------------------------------------------------------

record GRGeometryPromotionBoundary : Set where
  constructor gr-geometry-promotion-boundary
  field
    genericLenseThirringScalingClosesLiTorrMagnitude : Bool
    genericLenseThirringScalingClosesLiTorrMagnitudeIsFalse :
      genericLenseThirringScalingClosesLiTorrMagnitude ≡ false

    pointOneCubicMetreIllustrationIsUniqueApparatus : Bool
    pointOneCubicMetreIllustrationIsUniqueApparatusIsFalse :
      pointOneCubicMetreIllustrationIsUniqueApparatus ≡ false

    literalComparatorNeedsMassCurrentAndProbeGeometry : Bool
    literalComparatorNeedsMassCurrentAndProbeGeometryIsTrue :
      literalComparatorNeedsMassCurrentAndProbeGeometry ≡ true

    residualPromotionStillNeedsExternalMeasurement : Bool
    residualPromotionStillNeedsExternalMeasurementIsTrue :
      residualPromotionStillNeedsExternalMeasurement ≡ true

canonicalGRGeometryPromotionBoundary : GRGeometryPromotionBoundary
canonicalGRGeometryPromotionBoundary =
  gr-geometry-promotion-boundary false refl false refl true refl true refl
