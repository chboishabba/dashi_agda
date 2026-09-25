module DASHI.Reasoning.TrialecticGrothendieckTransportCoherenceExact where

------------------------------------------------------------------------
-- TRIALECTIC CHART TRANSPORT x GROTHENDIECK OVERLAP COHERENCE
--
-- DASHI CONTRIBUTION
--
-- The structured dialectic carrier is:
--
--   D = (leftCell , rightCell , synthesisCell) : T^9.
--
-- Its canonical cyclic chart transition is:
--
--   rotate D = (rightCell , synthesisCell , leftCell).
--
-- This transition is invertible with inverse rotate^2 and rotate^3 = id.
-- More importantly, it commutes exactly with the shared-overlap restriction:
--
--   leftCell (rotate D) = rightCell D.
--
-- Hence the transition from one dyadic chart to the next carries the previous
-- chart's right endpoint to the next chart's left endpoint definitionally.
--
-- For the canonical trialectic fixture:
--
--   AB = (A,B,C)
--   BC = (B,C,A)
--   CA = (C,A,B)
--
-- so cyclic transport sends AB -> BC -> CA -> AB exactly.
--
-- This is a concrete chart-transition groupoid action coherent with the
-- Grothendieck overlap maps.  It is NOT yet a groupoid-valued presheaf on the
-- full relational Grothendieck category: chart transitions between AB/BC/CA
-- are distinct from the site's restriction arrows AB->global and vertex->edge.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.RelationalSelfDescentExact as Existing
import DASHI.Core.RelationalTransportGroupoidActionExact as Groupoid
import DASHI.Foundations.RelationalStageTwelveGrothendieckExtensionExact as Site
import DASHI.Foundations.RelationalStageTwelveSiteExact as RelSheaf
import DASHI.Reasoning.TrialecticThreeCellHyperformSynthesisExact as Cell
import DASHI.Reasoning.TrialecticGrothendieckThreeCellDescentExact as GrothCell
import DASHI.Reasoning.TrialecticGrothendieckCellPresheafExact as Presheaf

------------------------------------------------------------------------
-- 1. Cyclic automorphism of one T^9 cell dialectic.
------------------------------------------------------------------------

rotateCell :
  Cell.CellDialectic →
  Cell.CellDialectic
rotateCell (Cell.cell-dialectic left right synthesis) =
  Cell.cell-dialectic right synthesis left

rotateCellTwice :
  Cell.CellDialectic →
  Cell.CellDialectic
rotateCellTwice dialectic = rotateCell (rotateCell dialectic)

rotateCellThrice :
  Cell.CellDialectic →
  Cell.CellDialectic
rotateCellThrice dialectic = rotateCell (rotateCellTwice dialectic)

rotateThreeIsIdentity :
  (dialectic : Cell.CellDialectic) →
  rotateCellThrice dialectic ≡ dialectic
rotateThreeIsIdentity
  (Cell.cell-dialectic left right synthesis) = refl

rotateTwiceAfterRotate :
  (dialectic : Cell.CellDialectic) →
  rotateCellTwice (rotateCell dialectic) ≡ dialectic
rotateTwiceAfterRotate
  (Cell.cell-dialectic left right synthesis) = refl

rotateAfterRotateTwice :
  (dialectic : Cell.CellDialectic) →
  rotateCell (rotateCellTwice dialectic) ≡ dialectic
rotateAfterRotateTwice
  (Cell.cell-dialectic left right synthesis) = refl

------------------------------------------------------------------------
-- 2. Source/target-indexed chart-transition homs.
------------------------------------------------------------------------

cyclicHom :
  (source target : Existing.RelationalPatch) →
  Groupoid.RelTransportHom Cell.CellDialectic source target
cyclicHom source target =
  Groupoid.rel-transport-hom
    rotateCell
    rotateCellTwice
    rotateTwiceAfterRotate
    rotateAfterRotateTwice
    "DASHI trialectic cyclic T9 chart transition"

transportABtoBC :
  Groupoid.RelTransportHom
    Cell.CellDialectic
    Existing.patchAB
    Existing.patchBC
transportABtoBC =
  cyclicHom Existing.patchAB Existing.patchBC

transportBCtoCA :
  Groupoid.RelTransportHom
    Cell.CellDialectic
    Existing.patchBC
    Existing.patchCA
transportBCtoCA =
  cyclicHom Existing.patchBC Existing.patchCA

transportCAtoAB :
  Groupoid.RelTransportHom
    Cell.CellDialectic
    Existing.patchCA
    Existing.patchAB
transportCAtoAB =
  cyclicHom Existing.patchCA Existing.patchAB

------------------------------------------------------------------------
-- 3. The canonical structured trialectic is one transport orbit.
------------------------------------------------------------------------

canonicalABtoBC :
  Groupoid.forward transportABtoBC Cell.canonicalCellAB
  ≡ Cell.canonicalCellBC
canonicalABtoBC = refl

canonicalBCtoCA :
  Groupoid.forward transportBCtoCA Cell.canonicalCellBC
  ≡ Cell.canonicalCellCA
canonicalBCtoCA = refl

canonicalCAtoAB :
  Groupoid.forward transportCAtoAB Cell.canonicalCellCA
  ≡ Cell.canonicalCellAB
canonicalCAtoAB = refl

canonicalThreeChartCycleCloses :
  Groupoid.forward transportCAtoAB
    (Groupoid.forward transportBCtoCA
      (Groupoid.forward transportABtoBC Cell.canonicalCellAB))
  ≡ Cell.canonicalCellAB
canonicalThreeChartCycleCloses = refl

threeChartTransportCompositionIsIdentity :
  Groupoid._≈_
    (Groupoid.composeHom transportCAtoAB
      (Groupoid.composeHom transportBCtoCA transportABtoBC))
    (Groupoid.identityHom Existing.patchAB)
threeChartTransportCompositionIsIdentity dialectic =
  rotateThreeIsIdentity dialectic

------------------------------------------------------------------------
-- 4. Exact overlap coherence.
--
-- The previous chart's right endpoint is literally the next chart's left
-- endpoint after cyclic transport.  This is the core restriction/transport
-- commuting square for the shared participant overlap.
------------------------------------------------------------------------

transportCarriesRightEndpointToNextLeft :
  (dialectic : Cell.CellDialectic) →
  Cell.leftCell
    (Groupoid.forward
      (cyclicHom Existing.patchAB Existing.patchBC)
      dialectic)
  ≡ Cell.rightCell dialectic
transportCarriesRightEndpointToNextLeft
  (Cell.cell-dialectic left right synthesis) = refl

transportCarriesSynthesisToNextRight :
  (dialectic : Cell.CellDialectic) →
  Cell.rightCell
    (Groupoid.forward
      (cyclicHom Existing.patchAB Existing.patchBC)
      dialectic)
  ≡ Cell.synthesisCell dialectic
transportCarriesSynthesisToNextRight
  (Cell.cell-dialectic left right synthesis) = refl

transportCarriesLeftToNextSynthesis :
  (dialectic : Cell.CellDialectic) →
  Cell.synthesisCell
    (Groupoid.forward
      (cyclicHom Existing.patchAB Existing.patchBC)
      dialectic)
  ≡ Cell.leftCell dialectic
transportCarriesLeftToNextSynthesis
  (Cell.cell-dialectic left right synthesis) = refl

------------------------------------------------------------------------
-- 5. Coherence with the actual Grothendieck triadic overlap system.
------------------------------------------------------------------------

canonicalBOverlapTransportCoherence :
  RelSheaf.abAtB GrothCell.cellOverlapSystem Cell.canonicalCellAB
  ≡
  RelSheaf.bcAtB GrothCell.cellOverlapSystem
    (Groupoid.forward transportABtoBC Cell.canonicalCellAB)
canonicalBOverlapTransportCoherence = refl

canonicalCOverlapTransportCoherence :
  RelSheaf.bcAtC GrothCell.cellOverlapSystem Cell.canonicalCellBC
  ≡
  RelSheaf.caAtC GrothCell.cellOverlapSystem
    (Groupoid.forward transportBCtoCA Cell.canonicalCellBC)
canonicalCOverlapTransportCoherence = refl

canonicalAOverlapTransportCoherence :
  RelSheaf.caAtA GrothCell.cellOverlapSystem Cell.canonicalCellCA
  ≡
  RelSheaf.abAtA GrothCell.cellOverlapSystem
    (Groupoid.forward transportCAtoAB Cell.canonicalCellCA)
canonicalAOverlapTransportCoherence = refl


------------------------------------------------------------------------
-- 5b. The same squares through the actual site-presheaf restrictions.
------------------------------------------------------------------------

presheafBRestrictionTransportSquare :
  (dialectic : Cell.CellDialectic) →
  Presheaf.restrict Site.bToBC
    (Groupoid.forward transportABtoBC dialectic)
  ≡
  Presheaf.restrict Site.bToAB dialectic
presheafBRestrictionTransportSquare
  (Cell.cell-dialectic left right synthesis) = refl

presheafCRestrictionTransportSquare :
  (dialectic : Cell.CellDialectic) →
  Presheaf.restrict Site.cToCA
    (Groupoid.forward transportBCtoCA dialectic)
  ≡
  Presheaf.restrict Site.cToBC dialectic
presheafCRestrictionTransportSquare
  (Cell.cell-dialectic left right synthesis) = refl

presheafARestrictionTransportSquare :
  (dialectic : Cell.CellDialectic) →
  Presheaf.restrict Site.aToAB
    (Groupoid.forward transportCAtoAB dialectic)
  ≡
  Presheaf.restrict Site.aToCA dialectic
presheafARestrictionTransportSquare
  (Cell.cell-dialectic left right synthesis) = refl

------------------------------------------------------------------------
-- 6. Relational-site object/chart crosswalk.
------------------------------------------------------------------------

data EdgeChart : Set where
  chartAB chartBC chartCA : EdgeChart

edgeChartObject : EdgeChart → Site.RelObj
edgeChartObject chartAB = Site.edgeAB
edgeChartObject chartBC = Site.edgeBC
edgeChartObject chartCA = Site.edgeCA

edgeChartPatch : EdgeChart → Existing.RelationalPatch
edgeChartPatch chartAB = Existing.patchAB
edgeChartPatch chartBC = Existing.patchBC
edgeChartPatch chartCA = Existing.patchCA

nextChart : EdgeChart → EdgeChart
nextChart chartAB = chartBC
nextChart chartBC = chartCA
nextChart chartCA = chartAB

chartTransition :
  (chart : EdgeChart) →
  Groupoid.RelTransportHom
    Cell.CellDialectic
    (edgeChartPatch chart)
    (edgeChartPatch (nextChart chart))
chartTransition chartAB = transportABtoBC
chartTransition chartBC = transportBCtoCA
chartTransition chartCA = transportCAtoAB

nextThreeCharts :
  (chart : EdgeChart) →
  nextChart (nextChart (nextChart chart)) ≡ chart
nextThreeCharts chartAB = refl
nextThreeCharts chartBC = refl
nextThreeCharts chartCA = refl

------------------------------------------------------------------------
-- 7. Important distinction: chart transition is not site restriction.
------------------------------------------------------------------------

data ChartTransitionIsGrothendieckRestrictionArrow : Set where
data EdgeTransitionGroupoidIsFullSitePresheaf : Set where

chartTransitionIsNotSilentlySiteRestriction :
  ChartTransitionIsGrothendieckRestrictionArrow → ⊥
chartTransitionIsNotSilentlySiteRestriction ()

edgeTransitionGroupoidDoesNotYetCreateFullSitePresheaf :
  EdgeTransitionGroupoidIsFullSitePresheaf → ⊥
edgeTransitionGroupoidDoesNotYetCreateFullSitePresheaf ()

record TrialecticGrothendieckTransportCoherenceBoundary : Set where
  constructor trialectic-grothendieck-transport-coherence-boundary
  field
    cyclicT9TransportConstructed : Bool
    cyclicTransportInvertible : Bool
    threeChartCycleCloses : Bool
    canonicalABBCTransportExact : Bool
    canonicalBCCAtransportExact : Bool
    canonicalCAABtransportExact : Bool
    sharedOverlapRestrictionCommutesWithTransport : Bool
    actualPresheafRestrictionSquaresCommute : Bool
    siteEdgeObjectsCrosswalkedToTransportPatches : Bool
    chartTransitionIdentifiedWithSiteRestriction : Bool
    fullGroupoidValuedSitePresheafConstructed : Bool

canonicalTrialecticGrothendieckTransportCoherenceBoundary :
  TrialecticGrothendieckTransportCoherenceBoundary
canonicalTrialecticGrothendieckTransportCoherenceBoundary =
  trialectic-grothendieck-transport-coherence-boundary
    true
    true
    true
    true
    true
    true
    true
    true
    true
    false
    false
