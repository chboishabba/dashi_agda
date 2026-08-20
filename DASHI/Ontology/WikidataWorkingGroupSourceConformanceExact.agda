module DASHI.Ontology.WikidataWorkingGroupSourceConformanceExact where

open import DASHI.Core.Prelude

import DASHI.Biology.AliceBrownCorpusLoom as Alice
import DASHI.Biology.EducationCorpusSourceRegistry as AliceSources
import DASHI.Core.AttributedSourceCore as Source
import DASHI.Education.EarlyYearsEmpowermentConnectednessSourceRegistry as EarlyYears
import DASHI.Ontology.WikidataWorkingGroupSourcePolicyExact as Policy
import DASHI.Semantics.SIOSemanticSurfaceBridge as SIO

------------------------------------------------------------------------
-- CONCRETE SOURCE-POLICY CONFORMANCE FOR THE WIKIDATA/JMD HANDOFF
--
-- The handoff has two source classes:
--
--   bibliographic/public sources
--     -> author/title/publication/year/DOI-state/URL/role/boundary;
--
--   executable/formal sources
--     -> source/archive identity + revision/content hash + exact contract.
--
-- Neither class self-promotes to theorem truth or edit/domain authority.
------------------------------------------------------------------------

sioRequirement : Policy.PublicSourceRequirement
sioRequirement = Policy.requireAttributedSource SIO.sio2014Source

earlyYearsStrategyRequirement : Policy.PublicSourceRequirement
earlyYearsStrategyRequirement =
  Policy.requireAttributedSource EarlyYears.earlyYearsStrategy2024Attributed

qualityArea6Requirement : Policy.PublicSourceRequirement
qualityArea6Requirement =
  Policy.requireAttributedSource EarlyYears.qualityArea6Attributed

brownKimberRequirement : Policy.PublicSourceRequirement
brownKimberRequirement =
  Policy.requireAttributedSource EarlyYears.brownKimber2026Attributed

jmdArchiveRequirement : Policy.PublicSourceRequirement
jmdArchiveRequirement =
  Policy.requirePinnedFormalSource
    "James Michael DuPont / Aristotle RequestProject archive ae06ae06-2580-422a-8fc3-92aeaaca8762"
    "archive SHA-256 d394cd224742dea06a47d2cc6c150e9284e2d6ea291a02c3ba2b2dd04d4f5f88; sorted RequestProject SHA-256 f5f0d6235e3bbf4fc881316900031f340accac75bb3825f10ed8d064f7c8ffda"
    "39-module SOURCE_MANIFEST.tsv + BRIDGE_CONTRACTS.tsv; exact theorem/checker names retained by LeanWikidata theorem/conformance bridges"

bfoSnapshotRequirement : Policy.PublicSourceRequirement
bfoSnapshotRequirement =
  Policy.requirePinnedFormalSource
    "Basic Formal Ontology 2020 OWL source"
    "BFO-ontology/BFO-2020 commit 0900316ea9d330f599bd110f7f6504ed33a87fc8"
    "continuant subclass entity; continuant disjointWith occurrent; transport into Wikidata remains inference-language/alignment gated"

------------------------------------------------------------------------
-- The full Alice corpus remains first-class provenance, not merely the one
-- Brown/Kimber row used by the early-years specialization.  Its owning source
-- registry carries eight distinct source-bound papers/items and the corpus loom
-- explicitly preserves source claims, cross-paper inferences, DASHI extensions
-- and future empirical work as different promotion levels.
------------------------------------------------------------------------

fullAliceCorpusRegistry : AliceSources.EducationCorpusSourceRegistry
fullAliceCorpusRegistry = AliceSources.canonicalEducationCorpusSourceRegistry

fullAliceCorpusLoom : Alice.AliceBrownCorpusLoom
fullAliceCorpusLoom = Alice.canonicalAliceBrownCorpusLoom

fullAliceCorpusSourceCountReading : Agda.Builtin.String.String
fullAliceCorpusSourceCountReading = Alice.canonicalCorpusLoomSourceCountReading

------------------------------------------------------------------------
-- Typed DOI-state witnesses on handoff-facing bibliographic sources.
------------------------------------------------------------------------

sioDOIRecorded : Source.DOIState
sioDOIRecorded = Source.doiState SIO.sio2014Source

brownKimberDOIRecorded : Source.DOIState
brownKimberDOIRecorded = Source.doiState EarlyYears.brownKimber2026Attributed

earlyYearsStrategyNoDOIAtlasLocal : Source.DOIState
earlyYearsStrategyNoDOIAtlasLocal = Source.doiState EarlyYears.earlyYearsStrategy2024Attributed

qualityArea6NoDOIAtlasLocal : Source.DOIState
qualityArea6NoDOIAtlasLocal = Source.doiState EarlyYears.qualityArea6Attributed

record WorkingGroupSourceConformanceBoundary : Set where
  constructor workingGroupSourceConformanceBoundary
  field
    fullAliceCorpusRetained : Bool
    sioTypedDOISourceRetained : Bool
    earlyYearsGovernmentNoDOIExplicit : Bool
    earlyYearsRegulatoryNoDOIExplicit : Bool
    brownKimberDOIRetained : Bool
    jmdArchiveHashAndContractRetained : Bool
    bfoRevisionAndContractRetained : Bool
    citationEqualsProof : Bool
    sourceCountEqualsTruthWeight : Bool
    sourceMetadataEqualsEditAuthority : Bool

canonicalWorkingGroupSourceConformanceBoundary : WorkingGroupSourceConformanceBoundary
canonicalWorkingGroupSourceConformanceBoundary =
  workingGroupSourceConformanceBoundary
    true true true true true true true false false false
