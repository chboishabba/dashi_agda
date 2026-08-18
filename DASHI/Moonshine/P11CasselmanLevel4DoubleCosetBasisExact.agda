module DASHI.Moonshine.P11CasselmanLevel4DoubleCosetBasisExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE / CONTEXT
--
-- Ralf Schmidt,
-- "Some remarks on local newforms for GL(2)",
-- Journal of the Ramanujan Mathematical Society 17 (2002), 115--147.
-- No DOI asserted here.
--
-- William Casselman,
-- "On some results of Atkin and Lehner",
-- Mathematische Annalen 201 (1973), 301--314.
-- DOI: 10.1007/BF01428197.
--
-- Schmidt Lemma 2.1.1 gives the explicit compact-model decomposition
--
--   K = disjoint union_{i=0}^n B(o) gamma_i K_2(n).
--
-- For n=2 there are exactly three support cells.  In the unramified PGL_2
-- representation these give the natural three-cell basis shape of the
-- K_0(4)=K_2(2)-fixed space.
--
-- DASHI CONTRIBUTION
-- Construct that finite basis carrier and place it beside, but NOT identify it
-- with, the three principal-level-2 projective branches already constructed in
-- P11Level44TwoAdicFixedVectorSeparationExact.
--
-- The remaining local theorem is now a concrete transform between:
--
--   Casselman cells   {valuation 0, valuation 1, terminal cell 2}
-- and
--   marked branches   P^1(F_2) = {1,2,4}.
--
-- Equal cardinality and a chosen labelling map are not promoted to a canonical
-- local representation-theoretic comparison.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Moonshine.CasselmanUnramifiedPGL2FixedVectorTowerExact as Casselman
import DASHI.Moonshine.P11Level44TwoAdicFixedVectorSeparationExact as Marked

------------------------------------------------------------------------
-- Source-native n=2 double-coset cell labels.
------------------------------------------------------------------------

data CasselmanLevel4Cell : Set where
  valuation0 valuation1 terminal2 : CasselmanLevel4Cell

casselmanCellIndex : CasselmanLevel4Cell → Nat
casselmanCellIndex valuation0 = 0
casselmanCellIndex valuation1 = 1
casselmanCellIndex terminal2 = 2

------------------------------------------------------------------------
-- A coordinate chart to the existing Old3 labels is useful bookkeeping, but
-- explicitly classified as a chosen chart rather than the missing JL map.
------------------------------------------------------------------------

data DegeneracyLabel124 : Set where
  d1 d2 d4 : DegeneracyLabel124

cellToDegeneracyLabel : CasselmanLevel4Cell → DegeneracyLabel124
cellToDegeneracyLabel valuation0 = d1
cellToDegeneracyLabel valuation1 = d2
cellToDegeneracyLabel terminal2 = d4

degeneracyLabelToCell : DegeneracyLabel124 → CasselmanLevel4Cell
degeneracyLabelToCell d1 = valuation0
degeneracyLabelToCell d2 = valuation1
degeneracyLabelToCell d4 = terminal2

cellDegeneracyRoundTrip :
  (cell : CasselmanLevel4Cell) →
  degeneracyLabelToCell (cellToDegeneracyLabel cell) ≡ cell
cellDegeneracyRoundTrip valuation0 = refl
cellDegeneracyRoundTrip valuation1 = refl
cellDegeneracyRoundTrip terminal2 = refl

degeneracyCellRoundTrip :
  (label : DegeneracyLabel124) →
  cellToDegeneracyLabel (degeneracyLabelToCell label) ≡ label
degeneracyCellRoundTrip d1 = refl
degeneracyCellRoundTrip d2 = refl
degeneracyCellRoundTrip d4 = refl

------------------------------------------------------------------------
-- Separate marked principal-level-2 branch carrier.
------------------------------------------------------------------------

casselmanCellToMarkedBranchChart : CasselmanLevel4Cell → Marked.P1F2
casselmanCellToMarkedBranchChart valuation0 = Marked.point1
casselmanCellToMarkedBranchChart valuation1 = Marked.point2
casselmanCellToMarkedBranchChart terminal2 = Marked.point4

markedBranchToCasselmanCellChart : Marked.P1F2 → CasselmanLevel4Cell
markedBranchToCasselmanCellChart Marked.point1 = valuation0
markedBranchToCasselmanCellChart Marked.point2 = valuation1
markedBranchToCasselmanCellChart Marked.point4 = terminal2

casselmanMarkedChartRoundTrip :
  (cell : CasselmanLevel4Cell) →
  markedBranchToCasselmanCellChart (casselmanCellToMarkedBranchChart cell) ≡ cell
casselmanMarkedChartRoundTrip valuation0 = refl
casselmanMarkedChartRoundTrip valuation1 = refl
casselmanMarkedChartRoundTrip terminal2 = refl

markedCasselmanChartRoundTrip :
  (branch : Marked.P1F2) →
  casselmanCellToMarkedBranchChart (markedBranchToCasselmanCellChart branch) ≡ branch
markedCasselmanChartRoundTrip Marked.point1 = refl
markedCasselmanChartRoundTrip Marked.point2 = refl
markedCasselmanChartRoundTrip Marked.point4 = refl

------------------------------------------------------------------------
-- Role separation: a chart between three-element label carriers does not make
-- Casselman's K_0(4) fixed vectors into principal full-level-2 fixed vectors.
------------------------------------------------------------------------

threeCasselmanCellsAgreeWithPublishedDimension :
  Casselman.fixedDimension Casselman.publishedP11LocalUnramifiedTower 2 ≡ 3
threeCasselmanCellsAgreeWithPublishedDimension = Casselman.level4FixedDimensionIsThree

record P11CasselmanLevel4DoubleCosetBasisBoundary : Set where
  field
    threeCasselmanCellsConstructed : Bool
    levelFourDimensionThreeSourceBacked : Bool
    markedThreeBranchChartConstructed : Bool
    chartDeclaredCanonicalJLComparison : Bool
    twoAdicTestVectorTransformStillRequired : Bool

canonicalP11CasselmanLevel4DoubleCosetBasisBoundary :
  P11CasselmanLevel4DoubleCosetBasisBoundary
canonicalP11CasselmanLevel4DoubleCosetBasisBoundary = record
  { threeCasselmanCellsConstructed = true
  ; levelFourDimensionThreeSourceBacked = true
  ; markedThreeBranchChartConstructed = true
  ; chartDeclaredCanonicalJLComparison = false
  ; twoAdicTestVectorTransformStillRequired = true
  }
