module DASHI.Wikimedia.IbrahimFirstLinkHistoricalDiscriminatorParetoExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Wikimedia.IbrahimFirstLinkProducerArchaeologyDeweyDoiQidExact as Producer

------------------------------------------------------------------------
-- IBRAHIM HISTORICAL FIRST-LINK DISCRIMINATOR / PARETO FRONTIER
--
-- We do not replay all 11M raw pages before we know which producer object we
-- are trying to reproduce.  The Pareto strategy is to use a small set of
-- primary-paper edges as source-owned oracles, then seek a minimal set of
-- snapshot-sensitive pages whose historical revisions discriminate the
-- released 20141008 producer cue from the paper's November-2014 corpus claim.
--
-- DOI / QID / Dewey / links travel with each probe but remain orthogonal to
-- historical edge payment.  Current Wikidata identity does not determine what
-- the 2014 first-link parser emitted.
------------------------------------------------------------------------

data ProbeRole : Set where
  primaryPaperOracle
  parserRegressionOracle
  snapshotDiscriminator
  methodCodeDiscriminator : ProbeRole

record HistoricalEdgeProbe : Set where
  constructor historical-edge-probe
  field
    rank : Nat
    role : ProbeRole
    childTitle : String
    childQid : String
    parentTitle : String
    parentQid : String
    childDewey : String
    parentDewey : String
    primarySource : String
    primaryLink : String
    historicalEdgePaid : Bool
    octoberCandidateChecked : Bool
    novemberCandidateChecked : Bool
    releasedParserReplayed : Bool
    informationGain : String
open HistoricalEdgeProbe public

trainRail : HistoricalEdgeProbe
trainRail = historical-edge-probe
  0 primaryPaperOracle
  "Train" "Q870"
  "rail transport" "Q3565868"
  "unresolved" "unresolved"
  "Ibrahim, Danforth, Dodds 2017, DOI 10.1016/j.jocs.2016.12.001; paper body explicitly states Train's first link is rail transport"
  "https://doi.org/10.1016/j.jocs.2016.12.001"
  true false false false
  "strong parser oracle because the paper names the edge explicitly; weak dump-date discriminator until October/November historical source revisions are compared"

bananaFruit : HistoricalEdgeProbe
bananaFruit = historical-edge-probe
  0 primaryPaperOracle
  "Banana" "Q503"
  "fruit" "Q1364"
  "unresolved" "unresolved"
  "Ibrahim, Danforth, Dodds 2017, DOI 10.1016/j.jocs.2016.12.001; paper body explicitly states Banana -> fruit"
  "https://doi.org/10.1016/j.jocs.2016.12.001"
  true false false false
  "primary-paper oracle; useful for parser semantics and title normalisation, but historical dump discrimination still requires candidate revision replay"

physicsNaturalScience : HistoricalEdgeProbe
physicsNaturalScience = historical-edge-probe
  0 primaryPaperOracle
  "Physics" "Q413"
  "natural science" "Q7991"
  "530" "500"
  "Ibrahim, Danforth, Dodds 2017, DOI 10.1016/j.jocs.2016.12.001; paper body explicitly states Physics -> natural science"
  "https://doi.org/10.1016/j.jocs.2016.12.001"
  true false false false
  "high-value Dewey/QID anchor because both endpoints have inspected present semantic coordinates while the historical first-link edge is independently source-owned by the paper"

bobDylanBlowin : HistoricalEdgeProbe
bobDylanBlowin = historical-edge-probe
  1 primaryPaperOracle
  "Bob Dylan" "Q392"
  "Blowin' in the Wind" "Q640529"
  "unresolved" "unresolved"
  "Ibrahim, Danforth, Dodds 2017, DOI 10.1016/j.jocs.2016.12.001; paper body explicitly states Bob Dylan -> Blowin' in the Wind"
  "https://doi.org/10.1016/j.jocs.2016.12.001"
  true false false false
  "useful lexical/title oracle because punctuation and title normalisation stress a different part of the parser/output path"

------------------------------------------------------------------------
-- Producer-level candidate distinction.
------------------------------------------------------------------------

record CandidateCorpus : Set where
  constructor candidate-corpus
  field
    label : String
    evidenceRole : String
    directLink : String
    sameObjectWithProductionInputPaid : Bool
open CandidateCorpus public

octoberCodeCue : CandidateCorpus
octoberCodeCue = candidate-corpus
  "English Wikipedia dump cue 2014-10-08"
  "released parser comment and older parser/test copies point at enwiki/20141008; implementation-lineage evidence only"
  "https://dumps.wikimedia.org/enwiki/20141008/"
  false

novemberPaperCorpus : CandidateCorpus
novemberPaperCorpus = candidate-corpus
  "English Wikipedia snapshot, November 2014"
  "primary paper, methods appendix, thesis and author blog repeatedly identify November 2014; month-level scientific provenance"
  "https://doi.org/10.1016/j.jocs.2016.12.001"
  false

------------------------------------------------------------------------
-- Pareto routing: choose the cheapest next acquisition with the highest chance
-- of collapsing multiple open producer hypotheses.
------------------------------------------------------------------------

data InvestigationTarget : Set where
  exactDumpLineage
  parserMethodEquivalence
  historicalEdgeReplay
  fullCorpusReplay : InvestigationTarget

record ParetoTarget : Set where
  constructor pareto-target
  field
    priority : Nat
    target : InvestigationTarget
    acquisition : String
    pays : String
    requiresFullCorpus : Bool
    currentState : String
open ParetoTarget public

firstTarget : ParetoTarget
firstTarget = pareto-target
  0 exactDumpLineage
  "locate a manifest, shell history, data note, checksum, filename, archive receipt or other same-object evidence joining full_wiki_data/small*.xml to an upstream enwiki dump"
  "October-vs-November producer identity; constrains every historical FLN edge and all downstream statistics at once"
  false
  Producer.firstCorpusIdentityResidual

secondTarget : ParetoTarget
secondTarget = pareto-target
  1 parserMethodEquivalence
  "locate the image/audio file-extension exclusion described in the methods appendix, or exhibit a historical page where extension filtering changes the first valid link"
  "released-code <-> described-method equivalence"
  false
  Producer.firstParserEquivalenceResidual

thirdTarget : ParetoTarget
thirdTarget = pareto-target
  2 historicalEdgeReplay
  "retrieve candidate October and November historical revisions for the primary-paper oracle pages and replay the released parser; prefer any page whose first link differs between candidates"
  "minimal historical discriminator set and parser-regression receipt"
  false
  "primary-paper edges are paid; candidate-snapshot replay is not"

fourthTarget : ParetoTarget
fourthTarget = pareto-target
  9 fullCorpusReplay
  "reconstruct all split XML inputs and replay the whole FLN only after exact producer identity and parser semantics are bounded"
  "whole-corpus reproduction"
  true
  "deliberately deferred because it is dominated by cheaper producer-lineage and discriminator tests"

------------------------------------------------------------------------
-- Current metadata coordinates inspected in this tranche.
------------------------------------------------------------------------

record MetadataCoordinate : Set where
  constructor metadata-coordinate
  field
    title : String
    qid : String
    dewey : String
    wikidataLink : String
    historicalEdgeAuthority : Bool
open MetadataCoordinate public

physicsCoordinate : MetadataCoordinate
physicsCoordinate = metadata-coordinate
  "physics" "Q413" "530" "https://www.wikidata.org/wiki/Q413" false

naturalScienceCoordinate : MetadataCoordinate
naturalScienceCoordinate = metadata-coordinate
  "natural science" "Q7991" "500" "https://www.wikidata.org/wiki/Q7991" false

trainCoordinate : MetadataCoordinate
trainCoordinate = metadata-coordinate
  "train" "Q870" "unresolved" "https://www.wikidata.org/wiki/Q870" false

railTransportCoordinate : MetadataCoordinate
railTransportCoordinate = metadata-coordinate
  "rail transport" "Q3565868" "unresolved" "https://www.wikidata.org/wiki/Q3565868" false

bananaCoordinate : MetadataCoordinate
bananaCoordinate = metadata-coordinate
  "banana" "Q503" "unresolved" "https://www.wikidata.org/wiki/Q503" false

fruitCoordinate : MetadataCoordinate
fruitCoordinate = metadata-coordinate
  "fruit (botanical concept used by current enwiki title)" "Q1364" "unresolved" "https://www.wikidata.org/wiki/Q1364" false

bobDylanCoordinate : MetadataCoordinate
bobDylanCoordinate = metadata-coordinate
  "Bob Dylan" "Q392" "unresolved" "https://www.wikidata.org/wiki/Q392" false

blowinCoordinate : MetadataCoordinate
blowinCoordinate = metadata-coordinate
  "Blowin' in the Wind" "Q640529" "unresolved" "https://www.wikidata.org/wiki/Q640529" false

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data PaperOracleIdentifiesDump : Set where
data CurrentQidIdentifiesHistoricalTitle : Set where
data DeweyClassifiesHistoricalEdge : Set where
data FourMatchingEdgesProveWholeCorpus : Set where
data OctoberCommentOverridesPrimaryPaper : Set where
data PaperMonthOverridesExecutedBytes : Set where

paperOracleDoesNotIdentifyDump : PaperOracleIdentifiesDump → ⊥
paperOracleDoesNotIdentifyDump ()

currentQidDoesNotIdentifyHistoricalTitle : CurrentQidIdentifiesHistoricalTitle → ⊥
currentQidDoesNotIdentifyHistoricalTitle ()

deweyDoesNotClassifyHistoricalEdge : DeweyClassifiesHistoricalEdge → ⊥
deweyDoesNotClassifyHistoricalEdge ()

fourEdgesDoNotProveWholeCorpus : FourMatchingEdgesProveWholeCorpus → ⊥
fourEdgesDoNotProveWholeCorpus ()

octoberCommentDoesNotOverridePaper : OctoberCommentOverridesPrimaryPaper → ⊥
octoberCommentDoesNotOverridePaper ()

paperMonthDoesNotOverrideBytes : PaperMonthOverridesExecutedBytes → ⊥
paperMonthDoesNotOverrideBytes ()

record HistoricalDiscriminatorBoundary : Set where
  constructor historical-discriminator-boundary
  field
    primaryPaperEdgesRetainedAsOracles : Bool
    doiTravels : Bool
    qidTravels : Bool
    deweyTravels : Bool
    directLinksTravel : Bool
    exactDumpStillUnpaid : Bool
    parserEquivalenceStillUnpaid : Bool
    fullReplayDeferredByPareto : Bool
    metadataPromotesHistoricalEdges : Bool
open HistoricalDiscriminatorBoundary public

canonicalHistoricalDiscriminatorBoundary : HistoricalDiscriminatorBoundary
canonicalHistoricalDiscriminatorBoundary =
  historical-discriminator-boundary
    true true true true true true true true false
