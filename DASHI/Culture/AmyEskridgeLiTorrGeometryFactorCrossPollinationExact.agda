module DASHI.Culture.AmyEskridgeLiTorrGeometryFactorCrossPollinationExact where

open import DASHI.Core.Prelude

import DASHI.Culture.AmyEskridgeLiTorrGRGeometryCrossPollinationExact as G
import DASHI.Physics.ExoticGravity.LiTorrIdealizedGeometryFactorBidiExact as F

------------------------------------------------------------------------
-- ESKRIDGE x LI/TORR GEOMETRY FACTOR
--
-- This bridge refines the magnitude discussion without claiming that
-- Eskridge, Li, or Torr specified the exact idealized source used here.
------------------------------------------------------------------------

record GeometryCrossPollination : Set where
  constructor geometry-cross-pollination
  field
    standardGRKernelOwned : Bool
    standardGRKernelOwnedIsTrue : standardGRKernelOwned ≡ true

    historicalExactGeometryStillOpen : Bool
    historicalExactGeometryStillOpenIsTrue : historicalExactGeometryStillOpen ≡ true

    naiveNfoldScalingInsufficient : Bool
    naiveNfoldScalingInsufficientIsTrue : naiveNfoldScalingInsufficient ≡ true

    geometryResolvedVectorIntegralRequired : Bool
    geometryResolvedVectorIntegralRequiredIsTrue :
      geometryResolvedVectorIntegralRequired ≡ true

canonicalGeometryCrossPollination : GeometryCrossPollination
canonicalGeometryCrossPollination =
  geometry-cross-pollination true refl true refl true refl true refl

geometryFactorFrontier : F.GeometryFactorLeaf
geometryFactorFrontier = F.currentFirstOpenGeometryFactorLeaf

------------------------------------------------------------------------
-- Promotion firewall.
------------------------------------------------------------------------

record GeometryPromotionBoundary : Set where
  constructor geometry-promotion-boundary
  field
    tenMinusNineArithmeticClosesExternalField : Bool
    tenMinusNineArithmeticClosesExternalFieldIsFalse :
      tenMinusNineArithmeticClosesExternalField ≡ false

    farFieldSameJWeldClosesHistoricalNearField : Bool
    farFieldSameJWeldClosesHistoricalNearFieldIsFalse :
      farFieldSameJWeldClosesHistoricalNearField ≡ false

    exactSourceAndProbeGeometryRequiredForMagnitudeWeld : Bool
    exactSourceAndProbeGeometryRequiredForMagnitudeWeldIsTrue :
      exactSourceAndProbeGeometryRequiredForMagnitudeWeld ≡ true

canonicalGeometryPromotionBoundary : GeometryPromotionBoundary
canonicalGeometryPromotionBoundary =
  geometry-promotion-boundary false refl false refl true refl
