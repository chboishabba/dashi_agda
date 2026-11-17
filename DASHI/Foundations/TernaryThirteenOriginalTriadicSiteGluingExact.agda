module DASHI.Foundations.TernaryThirteenOriginalTriadicSiteGluingExact where

------------------------------------------------------------------------
-- H2.02: source-written descent for the ALREADY-EXISTING non-discrete
-- Grothendieck A/B/C relational patch category. Import the original
-- topology, genuine cover, pullbacks, stability and transitivity.
--
-- The three charts share four-axis blocks (A,B,C) pairwise. A common
-- central trit must agree as an additional independent matching law.
-- This is the actual 3-chart descent construction, not an attempt to
-- recreate the topology or claim its group/Monster interpretation.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
import DASHI.Foundations.RelationalStageTwelveGrothendieckExtensionExact as Site
import DASHI.Foundations.StageTwelveGrothendieckRelationHyperformExact as Stage12
import DASHI.Foundations.StageAtlasZeroToEleven as Atlas
import DASHI.Foundations.TernaryThirteenFibreSplitExact as Words
import DASHI.Foundations.TernaryThirteenOriginalAxisValuationBridgeExact as Source
import DASHI.Foundations.TernaryThirteenFibrePunctureExact as Puncture
import DASHI.Foundations.TernaryThirteenOriginalPantsFrontierBridgeExact as Pants
import DASHI.Topology.TernaryPantsFrontierExact as Frontier
import DASHI.Biology.RelationalAppraisalPointedPhaseExact as Rel
import Base369 as Base

Block4 : Set
Block4 = Words.TritWord 4

GlobalTwelveCentre : Set
GlobalTwelveCentre =
  (Block4 × (Block4 × Block4)) × Base.TriTruth

PairChart : Set
PairChart = (Block4 × Block4) × Base.TriTruth

vertexBlock : PairChart → Block4
vertexBlock chart = proj₁ (proj₁ chart)

secondBlock : PairChart → Block4
secondBlock chart = proj₂ (proj₁ chart)

chartCentre : PairChart → Base.TriTruth
chartCentre = proj₂

globalA : GlobalTwelveCentre → Block4
globalA global = proj₁ (proj₁ global)

globalB : GlobalTwelveCentre → Block4
globalB global = proj₁ (proj₂ (proj₁ global))

globalC : GlobalTwelveCentre → Block4
globalC global = proj₂ (proj₂ (proj₁ global))

globalCentre : GlobalTwelveCentre → Base.TriTruth
globalCentre = proj₂

restrictAB : GlobalTwelveCentre → PairChart
restrictAB global =
  (globalA global , globalB global) , globalCentre global

restrictBC : GlobalTwelveCentre → PairChart
restrictBC global =
  (globalB global , globalC global) , globalCentre global

restrictCA : GlobalTwelveCentre → PairChart
restrictCA global =
  (globalC global , globalA global) , globalCentre global

record TriadicMatching
  (ab bc ca : PairChart) : Set where
  constructor triadic-matching
  field
    overlapB : secondBlock ab ≡ vertexBlock bc
    overlapC : secondBlock bc ≡ vertexBlock ca
    overlapA : secondBlock ca ≡ vertexBlock ab
    centreABBC : chartCentre ab ≡ chartCentre bc
    centreBCCA : chartCentre bc ≡ chartCentre ca
open TriadicMatching public

-- Construct one global three-block section and one central trit.
glueTriadic :
  (ab bc ca : PairChart) →
  TriadicMatching ab bc ca → GlobalTwelveCentre
glueTriadic ab bc ca matching =
  (vertexBlock ab , (secondBlock ab , secondBlock bc)) ,
  chartCentre ab

triadicABGlueRestricts :
  (ab bc ca : PairChart) (matching : TriadicMatching ab bc ca) →
  restrictAB (glueTriadic ab bc ca matching) ≡ ab
triadicABGlueRestricts ab bc ca matching = refl

triadicBCGlueRestricts :
  (ab bc ca : PairChart) (matching : TriadicMatching ab bc ca) →
  restrictBC (glueTriadic ab bc ca matching) ≡ bc
triadicBCGlueRestricts ((a , b) , centerAB)
  ((b' , c) , centerBC) ca matching =
  cong₂ _,_
    (cong₂ _,_
      (overlapB matching)
      refl)
    (centreABBC matching)

triadicCAGlueRestricts :
  (ab bc ca : PairChart) (matching : TriadicMatching ab bc ca) →
  restrictCA (glueTriadic ab bc ca matching) ≡ ca
triadicCAGlueRestricts ((a , b) , centerAB)
  bc ((c' , a') , centerCA) matching =
  cong₂ _,_
    (cong₂ _,_
      (trans (overlapC matching) refl)
      (sym (overlapA matching)))
    (trans (centreABBC matching) (centreBCCA matching))

triadicGlobalRestrictionMatches :
  (global : GlobalTwelveCentre) →
  TriadicMatching
    (restrictAB global)
    (restrictBC global)
    (restrictCA global)
triadicGlobalRestrictionMatches global =
  triadic-matching refl refl refl refl refl

triadicGlobalRoundTrip :
  (global : GlobalTwelveCentre) →
  glueTriadic
    (restrictAB global)
    (restrictBC global)
    (restrictCA global)
    (triadicGlobalRestrictionMatches global) ≡ global
triadicGlobalRoundTrip global = refl

-- The following source-valued morphisms are the existing nontrivial
-- cover and its original Grothendieck pullback theory, not invented.
selectedOriginalTriadicCover :
  Stage12.GrothendieckTopology.Cover
    Site.relationalTriadicTopology
    Site.triadicRelationalSieve
selectedOriginalTriadicCover = Site.triadicRelationalSieveCovers

selectedOriginalTriadicPullbackStable :
  {U V : Site.RelObj} →
  (arrow : Site.RelHom V U) →
  (sieve : Stage12.Sieve Site.relationalPatchCategory U) →
  Stage12.GrothendieckTopology.Cover
    Site.relationalTriadicTopology sieve →
  Stage12.GrothendieckTopology.Cover
    Site.relationalTriadicTopology
    (Stage12.pullbackSieve Site.relationalPatchCategory arrow sieve)
selectedOriginalTriadicPullbackStable =
  Stage12.GrothendieckTopology.stable Site.relationalTriadicTopology

-- Conversion from the actual 4+4+4 source-valuation word to
-- the existing source StageAtlas+central-coordinate model.
globalToSource :
  GlobalTwelveCentre → Rel.SourceCentralCompletionCarrier
globalToSource (((a , (b , c))) , centre) =
  Source.wordToValuation (Words.joinTriple 4 4 4 (a , (b , c))) ,
  centre

sourceToGlobal :
  Rel.SourceCentralCompletionCarrier → GlobalTwelveCentre
sourceToGlobal (valuation , centre) =
  Words.splitTriple 4 4 4 (Source.valuationToWord valuation) ,
  centre

sourceGlobalPointwiseRoundTrip :
  (state : Rel.SourceCentralCompletionCarrier)
  (axis : Atlas.StageAtlasZeroToEleven) →
  proj₁ (globalToSource (sourceToGlobal state)) axis
  ≡ proj₁ state axis
sourceGlobalPointwiseRoundTrip (valuation , centre) axis
  rewrite Words.joinTripleAfterSplit 4 4 4
    (Source.valuationToWord valuation) =
  Source.valuationPointwiseRoundTrip valuation axis

sourceGlobalCentreRoundTrip :
  (state : Rel.SourceCentralCompletionCarrier) →
  proj₂ (globalToSource (sourceToGlobal state)) ≡ proj₂ state
sourceGlobalCentreRoundTrip state = refl

globalSourceRoundTrip :
  (global : GlobalTwelveCentre) →
  sourceToGlobal (globalToSource global) ≡ global
globalSourceRoundTrip ((a , (b , c)) , centre) =
  cong (λ blocks → (blocks , centre))
    (trans
      (cong (Words.splitTriple 4 4 4)
        (Source.valuationWordRoundTrip
          (Words.joinTriple 4 4 4 (a , (b , c)))))
      (Words.splitTripleAfterJoin 4 4 4 a b c))

-- Puncture of the common centre is preserved by the triadic glue.
triadicPunctureGlue :
  (ab bc ca : PairChart)
  (matching : TriadicMatching ab bc ca) →
  ¬ (chartCentre ab ≡ Base.tri-mid) →
  ¬ (globalCentre (glueTriadic ab bc ca matching)
    ≡ Base.tri-mid)
triadicPunctureGlue ab bc ca matching neq = neq

------------------------------------------------------------------------
-- Non-discrete triadic site -> original depth-13 pants frontier.
------------------------------------------------------------------------

originalTriadicGlueToPants :
  (ab bc ca : PairChart) →
  TriadicMatching ab bc ca → Frontier.PantsPath 13
originalTriadicGlueToPants ab bc ca matching =
  Pants.sourceCentralToPants13
    (globalToSource (glueTriadic ab bc ca matching))

originalTriadicPantsRecoverAtlas :
  (ab bc ca : PairChart)
  (matching : TriadicMatching ab bc ca)
  (axis : Atlas.StageAtlasZeroToEleven) →
  proj₁
    (Pants.pants13ToSourceCentral
      (originalTriadicGlueToPants ab bc ca matching))
    axis
  ≡ proj₁ (globalToSource (glueTriadic ab bc ca matching)) axis
originalTriadicPantsRecoverAtlas ab bc ca matching axis =
  Pants.sourcePantsRoundTripOnAxis
    (globalToSource (glueTriadic ab bc ca matching)) axis

originalTriadicPantsRecoverCentre :
  (ab bc ca : PairChart)
  (matching : TriadicMatching ab bc ca) →
  proj₂
    (Pants.pants13ToSourceCentral
      (originalTriadicGlueToPants ab bc ca matching))
  ≡ chartCentre ab
originalTriadicPantsRecoverCentre ab bc ca matching =
  Pants.sourcePantsRoundTripOnCentre
    (globalToSource (glueTriadic ab bc ca matching))


------------------------------------------------------------------------
-- UNIQUENESS of the selected triadic covering-family glue:
-- AB fixes A,B and the centre, BC additionally fixes C; CA is the
-- overlap check. No function extensionality or proof irrelevance.
------------------------------------------------------------------------

triadicGluingUnique :
  (ab bc ca : PairChart)
  (matching : TriadicMatching ab bc ca)
  (candidate : GlobalTwelveCentre) →
  restrictAB candidate ≡ ab →
  restrictBC candidate ≡ bc →
  restrictCA candidate ≡ ca →
  candidate ≡ glueTriadic ab bc ca matching
triadicGluingUnique ab bc ca matching
  ((a , (b , c)) , centre) eqAB eqBC eqCA =
  cong₂ _,_
    (cong₂ _,_
      (cong (λ p → proj₁ (proj₁ p)) eqAB)
      (cong₂ _,_
        (cong (λ p → proj₂ (proj₁ p)) eqAB)
        (cong (λ p → proj₂ (proj₁ p)) eqBC)))
    (cong proj₂ eqAB)
