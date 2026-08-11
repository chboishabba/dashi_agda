module DASHI.Biology.PointedTernaryBulkExact where

open import DASHI.Core.Prelude

import DASHI.Biology.DialecticalSheetSpiralExact as Sheet
import DASHI.Biology.TernaryHypercubeHyperfabricExact as Hyper
import DASHI.Biology.TernaryMonsterSymmetryCandidateExact as Symmetry

------------------------------------------------------------------------
-- Exact carrier behind
--
--   196830 = 10 * 3^9 = (1 + 9) * 3^9.
--
-- The ten labels are not ten unexplained copies.  They are one unmarked sheet
-- plus a sheet with one of its nine sites marked.  This construction reuses the
-- repository's literal ternary 3 x 3 sheet and its square symmetries.
------------------------------------------------------------------------

data SheetSite : Set where
  northWestSite : SheetSite
  northSite : SheetSite
  northEastSite : SheetSite
  westSite : SheetSite
  centreSite : SheetSite
  eastSite : SheetSite
  southWestSite : SheetSite
  southSite : SheetSite
  southEastSite : SheetSite

MarkedOrUnmarkedSite : Set
MarkedOrUnmarkedSite = ⊤ ⊎ SheetSite

PointedTernarySheet : Set
PointedTernarySheet = MarkedOrUnmarkedSite × Sheet.Sheet3

siteCount : Nat
siteCount = 9

unmarkedCount : Nat
unmarkedCount = 1

markerCount : Nat
markerCount = unmarkedCount + siteCount

markerCountIsTen : markerCount ≡ 10
markerCountIsTen = refl

ternarySheetCount : Nat
ternarySheetCount = Hyper.ternaryLatticeCount 9

ternarySheetCountIs19683 : ternarySheetCount ≡ 19683
ternarySheetCountIs19683 = refl

pointedBulkDimension : Nat
pointedBulkDimension = markerCount * ternarySheetCount

pointedBulkDimensionIs196830 : pointedBulkDimension ≡ 196830
pointedBulkDimensionIs196830 = refl

unpointedPlusPointedDimension : Nat
unpointedPlusPointedDimension =
  ternarySheetCount + siteCount * ternarySheetCount

unpointedPlusPointedDimensionIs196830 :
  unpointedPlusPointedDimension ≡ 196830
unpointedPlusPointedDimensionIs196830 = refl

pointedBulkEqualsUnpointedPlusPointed :
  pointedBulkDimension ≡ unpointedPlusPointedDimension
pointedBulkEqualsUnpointedPlusPointed = refl

ternaryElevenCount : Nat
ternaryElevenCount = Hyper.ternaryLatticeCount 11

pointedBulkEqualsThreeNinePlusThreeEleven :
  pointedBulkDimension ≡ ternarySheetCount + ternaryElevenCount
pointedBulkEqualsThreeNinePlusThreeEleven = refl

------------------------------------------------------------------------
-- Literal D4 generators on the marker coordinate.  The site action is chosen
-- to agree with DialecticalSheetSpiralExact.rotateQuarter and reflectVertical.
------------------------------------------------------------------------

rotateSiteQuarter : SheetSite → SheetSite
rotateSiteQuarter northWestSite = northEastSite
rotateSiteQuarter northSite = eastSite
rotateSiteQuarter northEastSite = southEastSite
rotateSiteQuarter westSite = northSite
rotateSiteQuarter centreSite = centreSite
rotateSiteQuarter eastSite = southSite
rotateSiteQuarter southWestSite = northWestSite
rotateSiteQuarter southSite = westSite
rotateSiteQuarter southEastSite = southWestSite

reflectSiteVertical : SheetSite → SheetSite
reflectSiteVertical northWestSite = northEastSite
reflectSiteVertical northSite = northSite
reflectSiteVertical northEastSite = northWestSite
reflectSiteVertical westSite = eastSite
reflectSiteVertical centreSite = centreSite
reflectSiteVertical eastSite = westSite
reflectSiteVertical southWestSite = southEastSite
reflectSiteVertical southSite = southSite
reflectSiteVertical southEastSite = southWestSite

rotateSiteFour : SheetSite → SheetSite
rotateSiteFour site =
  rotateSiteQuarter
    (rotateSiteQuarter
      (rotateSiteQuarter
        (rotateSiteQuarter site)))

rotateSiteFourReturns : (site : SheetSite) → rotateSiteFour site ≡ site
rotateSiteFourReturns northWestSite = refl
rotateSiteFourReturns northSite = refl
rotateSiteFourReturns northEastSite = refl
rotateSiteFourReturns westSite = refl
rotateSiteFourReturns centreSite = refl
rotateSiteFourReturns eastSite = refl
rotateSiteFourReturns southWestSite = refl
rotateSiteFourReturns southSite = refl
rotateSiteFourReturns southEastSite = refl

reflectionSiteIsInvolutive :
  (site : SheetSite) →
  reflectSiteVertical (reflectSiteVertical site) ≡ site
reflectionSiteIsInvolutive northWestSite = refl
reflectionSiteIsInvolutive northSite = refl
reflectionSiteIsInvolutive northEastSite = refl
reflectionSiteIsInvolutive westSite = refl
reflectionSiteIsInvolutive centreSite = refl
reflectionSiteIsInvolutive eastSite = refl
reflectionSiteIsInvolutive southWestSite = refl
reflectionSiteIsInvolutive southSite = refl
reflectionSiteIsInvolutive southEastSite = refl

rotateMarkerQuarter : MarkedOrUnmarkedSite → MarkedOrUnmarkedSite
rotateMarkerQuarter (inj₁ tt) = inj₁ tt
rotateMarkerQuarter (inj₂ site) = inj₂ (rotateSiteQuarter site)

reflectMarkerVertical : MarkedOrUnmarkedSite → MarkedOrUnmarkedSite
reflectMarkerVertical (inj₁ tt) = inj₁ tt
reflectMarkerVertical (inj₂ site) = inj₂ (reflectSiteVertical site)

rotateMarkerFour : MarkedOrUnmarkedSite → MarkedOrUnmarkedSite
rotateMarkerFour marker =
  rotateMarkerQuarter
    (rotateMarkerQuarter
      (rotateMarkerQuarter
        (rotateMarkerQuarter marker)))

rotateMarkerFourReturns :
  (marker : MarkedOrUnmarkedSite) → rotateMarkerFour marker ≡ marker
rotateMarkerFourReturns (inj₁ tt) = refl
rotateMarkerFourReturns (inj₂ site)
  with rotateSiteFourReturns site
... | refl = refl

reflectionMarkerIsInvolutive :
  (marker : MarkedOrUnmarkedSite) →
  reflectMarkerVertical (reflectMarkerVertical marker) ≡ marker
reflectionMarkerIsInvolutive (inj₁ tt) = refl
reflectionMarkerIsInvolutive (inj₂ site)
  with reflectionSiteIsInvolutive site
... | refl = refl

rotatePointedQuarter : PointedTernarySheet → PointedTernarySheet
rotatePointedQuarter (marker , sheet) =
  rotateMarkerQuarter marker , Sheet.rotateQuarter sheet

reflectPointedVertical : PointedTernarySheet → PointedTernarySheet
reflectPointedVertical (marker , sheet) =
  reflectMarkerVertical marker , Sheet.reflectVertical sheet

rotatePointedFour : PointedTernarySheet → PointedTernarySheet
rotatePointedFour state =
  rotatePointedQuarter
    (rotatePointedQuarter
      (rotatePointedQuarter
        (rotatePointedQuarter state)))

rotatePointedFourReturns :
  (state : PointedTernarySheet) → rotatePointedFour state ≡ state
rotatePointedFourReturns (marker , Sheet.sheet3 a b c d e f g h i)
  with rotateMarkerFourReturns marker
... | refl = refl

reflectionPointedIsInvolutive :
  (state : PointedTernarySheet) →
  reflectPointedVertical (reflectPointedVertical state) ≡ state
reflectionPointedIsInvolutive (marker , Sheet.sheet3 a b c d e f g h i)
  with reflectionMarkerIsInvolutive marker
... | refl = refl

------------------------------------------------------------------------
-- Representation-dimension bookkeeping.  Adding the fixed unmarked marker
-- adds one A1 copy to the existing raw nine-site permutation representation:
--
--   R[D10] = 4 A1 + B1 + B2 + 2 E,
--
-- while A2 remains absent.  The five available D4 irrep species therefore do
-- not justify a 5 x 2 decomposition of this concrete ten-carrier.
------------------------------------------------------------------------

pointedMultiplicity : Symmetry.D4IrrepKind → Nat
pointedMultiplicity Symmetry.A1 =
  suc (Symmetry.rawNineMultiplicity Symmetry.A1)
pointedMultiplicity Symmetry.A2 =
  Symmetry.rawNineMultiplicity Symmetry.A2
pointedMultiplicity Symmetry.B1 =
  Symmetry.rawNineMultiplicity Symmetry.B1
pointedMultiplicity Symmetry.B2 =
  Symmetry.rawNineMultiplicity Symmetry.B2
pointedMultiplicity Symmetry.E2 =
  Symmetry.rawNineMultiplicity Symmetry.E2

pointedContribution : Symmetry.D4IrrepKind → Nat
pointedContribution kind =
  pointedMultiplicity kind * Symmetry.irrepDimension kind

pointedRepresentationDimension : Nat
pointedRepresentationDimension =
  pointedContribution Symmetry.A1
  + pointedContribution Symmetry.A2
  + pointedContribution Symmetry.B1
  + pointedContribution Symmetry.B2
  + pointedContribution Symmetry.E2

pointedRepresentationDimensionIsTen :
  pointedRepresentationDimension ≡ 10
pointedRepresentationDimensionIsTen = refl

pointedA1MultiplicityIsFour :
  pointedMultiplicity Symmetry.A1 ≡ 4
pointedA1MultiplicityIsFour = refl

pointedA2MultiplicityIsZero :
  pointedMultiplicity Symmetry.A2 ≡ 0
pointedA2MultiplicityIsZero = refl

record PointedTernaryBulkBoundary : Set where
  constructor pointedTernaryBulkBoundary
  field
    tenCarrierIsUnmarkedPlusNineMarkedSites : Bool
    tenCarrierIsUnmarkedPlusNineMarkedSitesIsTrue :
      tenCarrierIsUnmarkedPlusNineMarkedSites ≡ true

    tenCarrierIsAlreadyFiveIrrepPairs : Bool
    tenCarrierIsAlreadyFiveIrrepPairsIsFalse :
      tenCarrierIsAlreadyFiveIrrepPairs ≡ false

    rawPointedCarrierContainsA2 : Bool
    rawPointedCarrierContainsA2IsFalse :
      rawPointedCarrierContainsA2 ≡ false

    pointedBulkIsAlreadyMonsterModule : Bool
    pointedBulkIsAlreadyMonsterModuleIsFalse :
      pointedBulkIsAlreadyMonsterModule ≡ false

    squareGeneratorActionIsConcrete : Bool
    squareGeneratorActionIsConcreteIsTrue :
      squareGeneratorActionIsConcrete ≡ true

open PointedTernaryBulkBoundary public

canonicalPointedTernaryBulkBoundary : PointedTernaryBulkBoundary
canonicalPointedTernaryBulkBoundary =
  pointedTernaryBulkBoundary
    true refl
    false refl
    false refl
    false refl
    true refl
