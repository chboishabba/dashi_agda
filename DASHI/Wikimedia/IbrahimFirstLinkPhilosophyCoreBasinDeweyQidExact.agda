module DASHI.Wikimedia.IbrahimFirstLinkPhilosophyCoreBasinDeweyQidExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Wikimedia.IbrahimFirstLinkProducerRevisionArchaeologyExact as Producer
import DASHI.Wikimedia.IbrahimFirstLinkPrimarySourceDeweyQidDoiBidiExact as Primary

------------------------------------------------------------------------
-- IBRAHIM HISTORICAL PHILOSOPHY-CORE BASIN / 7-CYCLE
--
-- First-party result carrier:
-- https://compstorylab.org/share/papers/ibrahim2016a/notebooks/basins.html
--
-- The notebook loads the released FLN, traverses first links until the next
-- link repeats, and prints the top basin beginning at Awareness as:
-- Awareness -> Conscious -> Consciousness -> Quality (philosophy) ->
-- Philosophy -> Reality -> Existence
--
-- Since traversal stops exactly when the next FL repeats, the seven distinct
-- nodes followed by termination pay the closure Existence -> Awareness.
-- This is a historical November-2014 FLN result, not a claim about current
-- Wikipedia or about philosophical truth/ontology.
------------------------------------------------------------------------

record SnowballAttribution : Set where
  constructor snowball-attribution
  field
    authors : String
    title : String
    publication : String
    stableId : String
    primaryLink : String
    sourceRole : String
    boundedClaim : String
    excludedPromotion : String
    claimOwner : String
open SnowballAttribution public

primaryPaper : SnowballAttribution
primaryPaper = snowball-attribution
  "Mark Ibrahim; Christopher M. Danforth; Peter Sheridan Dodds"
  "Connecting every bit of knowledge: The structure of Wikipedia's First Link Network"
  "Journal of Computational Science 19 (2017), 21-30"
  "DOI 10.1016/j.jocs.2016.12.001; arXiv:1605.00309"
  "https://doi.org/10.1016/j.jocs.2016.12.001"
  "peer-reviewed primary scientific source"
  "owns the historical FLN construction and analysis family"
  "paper-level attribution does not by itself pay each concrete edge or exact runtime revision"
  "externalSourceOwner"

basinNotebook : SnowballAttribution
basinNotebook = snowball-attribution
  "Mark Ibrahim / Computational Story Lab"
  "Basins - Wikipedia First Link Network online appendix notebook"
  "official online appendix to Ibrahim-Danforth-Dodds"
  "first-party notebook artifact"
  "https://compstorylab.org/share/papers/ibrahim2016a/notebooks/basins.html"
  "first-party historical result/output and executable-analysis surface"
  "loads fln.json; defines traversal stop-on-repeat semantics; prints the seven-node inner philosophy basin and states top basins are based around it"
  "does not assert ontological equivalence, philosophical correctness, current-Wikipedia persistence or current page identity"
  "externalProducerOwner"

releasedFln : SnowballAttribution
releasedFln = snowball-attribution
  "Computational Story Lab / Ibrahim-Danforth-Dodds"
  "First Link Network Map (article -> first link)"
  "official online appendix data release"
  "data/fln.json; advertised 505 MB"
  "https://compstorylab.org/share/papers/ibrahim2016a/data/fln.json"
  "first-party released graph data"
  "underlying historical graph consumed by the basin notebook"
  "release identity does not establish exact dump ancestry or byte-equivalent local regeneration"
  "externalProducerOwner"

------------------------------------------------------------------------
-- Historical graph carrier.
------------------------------------------------------------------------

data CoreNode : Set where
  awareness
  conscious
  consciousness
  qualityPhilosophy
  philosophy
  reality
  existence : CoreNode

record HistoricalFirstLinkEdge : Set where
  constructor historical-edge
  field
    source : CoreNode
    target : CoreNode
    sourceReceipt : String
    paid : Bool
open HistoricalFirstLinkEdge public

awarenessToConscious : HistoricalFirstLinkEdge
awarenessToConscious = historical-edge awareness conscious
  "basins notebook rank-0 path; released FLN consumer" true

consciousToConsciousness : HistoricalFirstLinkEdge
consciousToConsciousness = historical-edge conscious consciousness
  "basins notebook rank-0 path; released FLN consumer" true

consciousnessToQuality : HistoricalFirstLinkEdge
consciousnessToQuality = historical-edge consciousness qualityPhilosophy
  "basins notebook rank-0 path; released FLN consumer" true

qualityToPhilosophy : HistoricalFirstLinkEdge
qualityToPhilosophy = historical-edge qualityPhilosophy philosophy
  "basins notebook rank-0 path; released FLN consumer" true

philosophyToReality : HistoricalFirstLinkEdge
philosophyToReality = historical-edge philosophy reality
  "basins notebook rank-0 path; released FLN consumer" true

realityToExistence : HistoricalFirstLinkEdge
realityToExistence = historical-edge reality existence
  "basins notebook rank-0 path; released FLN consumer" true

existenceToAwareness : HistoricalFirstLinkEdge
existenceToAwareness = historical-edge existence awareness
  "closure paid by notebook traverse semantics: rank-0 path lists seven distinct nodes and traversal stops only when next FL repeats" true

coreCycleLength : Nat
coreCycleLength = 7

coreCyclePaid : Bool
coreCyclePaid = true

historicalCycle : String
historicalCycle =
  "Awareness -> Conscious -> Consciousness -> Quality (philosophy) -> Philosophy -> Reality -> Existence -> Awareness"

------------------------------------------------------------------------
-- Traversal-visit / basin context. These are historical network statistics,
-- not philosophical weights.
------------------------------------------------------------------------

record BasinReceipt : Set where
  constructor basin-receipt
  field
    startTitle : String
    traversalVisits : Nat
    historicalPath : String
open BasinReceipt public

awarenessBasin : BasinReceipt
awarenessBasin = basin-receipt
  "Awareness" 7400884
  "Awareness -> Conscious -> Consciousness -> Quality (philosophy) -> Philosophy -> Reality -> Existence"

modernPhilosophyBasin : BasinReceipt
modernPhilosophyBasin = basin-receipt
  "Modern philosophy" 7269255
  "Modern philosophy -> Philosophy -> Reality -> Existence -> Awareness -> Conscious -> Consciousness -> Quality (philosophy)"

scienceBasin : BasinReceipt
scienceBasin = basin-receipt
  "Science" 4633960
  "Science -> Knowledge -> Fact -> Experience -> Experiment -> Hypothesis -> Explanation -> Set (mathematics) -> Mathematics -> Quantity -> Property (philosophy) -> Modern philosophy -> Philosophy -> Reality -> Existence -> Awareness -> Conscious -> Consciousness -> Quality (philosophy)"

socialScienceBasin : BasinReceipt
socialScienceBasin = basin-receipt
  "Social science" 417078
  "Social science -> Science -> Knowledge -> Fact -> Experience -> Experiment -> Hypothesis -> Explanation -> Set (mathematics) -> Mathematics -> Quantity -> Property (philosophy) -> Modern philosophy -> Philosophy -> Reality -> Existence -> Awareness -> Conscious -> Consciousness -> Quality (philosophy)"

------------------------------------------------------------------------
-- QID + Dewey navigation coordinates.
-- Current Wikidata identity is intentionally separate from 2014 page identity.
------------------------------------------------------------------------

record ExternalCoordinate : Set where
  constructor external-coordinate
  field
    historicalTitle : String
    currentQid : String
    qidLink : String
    dewey : String
    deweyReceipt : String
    exactQidPaid : Bool
    exactDeweyPaid : Bool
open ExternalCoordinate public

awarenessCoordinate : ExternalCoordinate
awarenessCoordinate = external-coordinate
  "Awareness" "Q4338318" "https://www.wikidata.org/wiki/Q4338318"
  "unresolved" "no exact inspected DDC promoted in this pass" true false

consciousCoordinate : ExternalCoordinate
consciousCoordinate = external-coordinate
  "Conscious" "unresolved"
  "https://en.wikipedia.org/wiki/Conscious_(disambiguation)"
  "unresolved"
  "historical title is revision-sensitive and current surface is disambiguating; no nearby identity/classification promoted"
  false false

consciousnessCoordinate : ExternalCoordinate
consciousnessCoordinate = external-coordinate
  "Consciousness" "Q7087" "https://www.wikidata.org/wiki/Q7087"
  "170" "Wikidata Q7087 DDC statement inspected 2026-09-11; classification retained as external metadata only" true true

qualityCoordinate : ExternalCoordinate
qualityCoordinate = external-coordinate
  "Quality (philosophy)" "Q1207505" "https://www.wikidata.org/wiki/Q1207505"
  "unresolved" "no exact inspected DDC promoted in this pass" true false

philosophyCoordinate : ExternalCoordinate
philosophyCoordinate = external-coordinate
  "Philosophy" "Q5891" "https://www.wikidata.org/wiki/Q5891"
  "100" "existing Ibrahim high-flow QID/DDC ledger; exact inspected DDC" true true

realityCoordinate : ExternalCoordinate
realityCoordinate = external-coordinate
  "Reality" "Q9510" "https://www.wikidata.org/wiki/Q9510"
  "111" "Wikidata Q9510 DDC statement inspected 2026-09-11" true true

existenceCoordinate : ExternalCoordinate
existenceCoordinate = external-coordinate
  "Existence" "Q468777" "https://www.wikidata.org/wiki/Q468777"
  "111.1" "Wikidata Q468777 DDC statement inspected 2026-09-11" true true

------------------------------------------------------------------------
-- Consumer / revision state.
------------------------------------------------------------------------

record PhilosophyCoreState : Set where
  constructor philosophy-core-state
  field
    sevenHistoricalEdgesPaid : Bool
    closurePaidFromTraversalSemantics : Bool
    primaryPaperDoiPaid : Bool
    firstPartyNotebookLinkPaid : Bool
    releasedFlnLinkPaid : Bool
    currentQidCoordinatesPartial : Bool
    exactDeweyCoordinatesPartial : Bool
    exactDumpAncestryPaid : Bool
    exactExtractionRevisionPaid : Bool
    currentWikipediaCyclePaid : Bool
    philosophicalOntologyPaid : Bool
open PhilosophyCoreState public

currentPhilosophyCoreState : PhilosophyCoreState
currentPhilosophyCoreState = philosophy-core-state
  true true true true true true true false false false false

firstUnpaidGraphReproductionJoin : String
firstUnpaidGraphReproductionJoin = Producer.firstUnpaidProducerJoin

firstUnpaidHistoricalIdentityJoin : String
firstUnpaidHistoricalIdentityJoin =
  "bind each November-2014 article/page identity to exact revision/page-id provenance if a consumer needs page-level historical identity rather than title-level FLN identity"

nextHighestAlphaGraphQuestion : String
nextHighestAlphaGraphQuestion =
  "test which of the seven historical core first-link edges persist, redirect or break in current Wikipedia, but keep drift observations separate from the 2014 cycle and from exact producer reproduction"

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data CycleMeansOntologicalEquivalence : Set where
data TraversalVisitsMeanTruth : Set where
data TraversalVisitsMeanAuthority : Set where
data PhilosophyDeweyPropagatesToCycle : Set where
data QidMeansHistoricalPageIdentity : Set where
data CurrentPageMeansHistoricalEdge : Set where
data BasinMeansTaxonomicParent : Set where

cycleDoesNotCreateOntologicalEquivalence : CycleMeansOntologicalEquivalence → ⊥
cycleDoesNotCreateOntologicalEquivalence ()

visitsDoNotCreateTruth : TraversalVisitsMeanTruth → ⊥
visitsDoNotCreateTruth ()

visitsDoNotCreateAuthority : TraversalVisitsMeanAuthority → ⊥
visitsDoNotCreateAuthority ()

philosophyDeweyDoesNotPropagate : PhilosophyDeweyPropagatesToCycle → ⊥
philosophyDeweyDoesNotPropagate ()

qidDoesNotCreateHistoricalPageIdentity : QidMeansHistoricalPageIdentity → ⊥
qidDoesNotCreateHistoricalPageIdentity ()

currentPageDoesNotCreateHistoricalEdge : CurrentPageMeansHistoricalEdge → ⊥
currentPageDoesNotCreateHistoricalEdge ()

basinDoesNotCreateTaxonomicParent : BasinMeansTaxonomicParent → ⊥
basinDoesNotCreateTaxonomicParent ()

producerState : Producer.ProducerReproductionState
producerState = Producer.currentProducerReproductionState

primaryBoundary : Primary.FirstLinkDeweyQidDoiBoundary
primaryBoundary = Primary.canonicalFirstLinkDeweyQidDoiBoundary
