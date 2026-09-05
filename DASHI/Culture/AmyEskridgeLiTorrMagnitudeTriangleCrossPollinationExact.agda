module DASHI.Culture.AmyEskridgeLiTorrMagnitudeTriangleCrossPollinationExact where

open import DASHI.Core.Prelude

import DASHI.Culture.AmyEskridgeLiTorrMechanismBridgeExact as E
import DASHI.Physics.ExoticGravity.LiTorrMagnitudeTriangleBidiExact as T
import DASHI.Physics.ExoticGravity.LiTorrStandardGRComparatorBidiExact as G
import DASHI.Physics.ExoticGravity.SuperconductingGravityCouplingResidualBidiExact as A

------------------------------------------------------------------------
-- ESKRIDGE x LI/TORR QUANTITATIVE TRIANGLE
--
-- This cross-pollination keeps three layers distinct:
--   historical/public mechanism discussion,
--   quantitative theoretical/correction comparison,
--   experimental promotion of a nonzero coupling residual.
------------------------------------------------------------------------

record EskridgeQuantitativeCrossPollination : Set where
  constructor eskridge-quantitative-cross-pollination
  field
    historicalMechanismBridgeOwned : Bool
    historicalMechanismBridgeOwnedIsTrue :
      historicalMechanismBridgeOwned ≡ true

    magnitudeTriangleOwned : Bool
    magnitudeTriangleOwnedIsTrue : magnitudeTriangleOwned ≡ true

    sameApparatusGRComparatorRequired : Bool
    sameApparatusGRComparatorRequiredIsTrue :
      sameApparatusGRComparatorRequired ≡ true

    alphaResidualRemainsExperimental : Bool
    alphaResidualRemainsExperimentalIsTrue :
      alphaResidualRemainsExperimental ≡ true

canonicalEskridgeQuantitativeCrossPollination : EskridgeQuantitativeCrossPollination
canonicalEskridgeQuantitativeCrossPollination =
  eskridge-quantitative-cross-pollination true refl true refl true refl true refl

------------------------------------------------------------------------
-- Reuse the current exact BIDI frontiers rather than restating them.
------------------------------------------------------------------------

magnitudeFrontier : T.MagnitudeLeaf
magnitudeFrontier = T.currentFirstOpenMagnitudeLeaf

standardGRFrontier : G.GRComparatorLeaf
standardGRFrontier = G.currentFirstOpenGRComparatorLeaf

alphaFrontier : A.AlphaLeaf
alphaFrontier = A.currentFirstOpenAlphaLeaf

------------------------------------------------------------------------
-- Strong promotion firewall.
------------------------------------------------------------------------

record EskridgeMagnitudePromotionBoundary : Set where
  constructor eskridge-magnitude-promotion-boundary
  field
    publicAdvocacyPlusHistoricalEquationsClosesPhysics : Bool
    publicAdvocacyPlusHistoricalEquationsClosesPhysicsIsFalse :
      publicAdvocacyPlusHistoricalEquationsClosesPhysics ≡ false

    criticMagnitudeReductionClosesExactZero : Bool
    criticMagnitudeReductionClosesExactZeroIsFalse :
      criticMagnitudeReductionClosesExactZero ≡ false

    sameApparatusGRBaselinePlusBackgroundClosureRequired : Bool
    sameApparatusGRBaselinePlusBackgroundClosureRequiredIsTrue :
      sameApparatusGRBaselinePlusBackgroundClosureRequired ≡ true

    reproducibleExternalScalingRequiredForAlphaPromotion : Bool
    reproducibleExternalScalingRequiredForAlphaPromotionIsTrue :
      reproducibleExternalScalingRequiredForAlphaPromotion ≡ true

canonicalEskridgeMagnitudePromotionBoundary : EskridgeMagnitudePromotionBoundary
canonicalEskridgeMagnitudePromotionBoundary =
  eskridge-magnitude-promotion-boundary false refl false refl true refl true refl
