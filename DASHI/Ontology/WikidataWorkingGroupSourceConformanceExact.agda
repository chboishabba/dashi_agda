module DASHI.Ontology.WikidataWorkingGroupSourceConformanceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Biology.AliceBrownCorpusLoom as Alice
import DASHI.Biology.EducationCorpusSourceRegistry as AliceSources
import DASHI.Core.AttributedSourceCore as Source
import DASHI.Education.EarlyYearsEmpowermentConnectednessSourceRegistry as EarlyYears
import DASHI.Ontology.WikidataWorkingGroupSourcePolicyExact as Policy
import DASHI.Semantics.SIOSemanticSurfaceBridge as SIO

------------------------------------------------------------------------
-- CONCRETE SOURCE-POLICY CONFORMANCE FOR THE WIKIDATA/JMD HANDOFF
------------------------------------------------------------------------

sioRequirement : Policy.PublicSourceRequirement
sioRequirement = Policy.requireAttributedSource SIO.sio2014Source

earlyYearsStrategyRequirement : Policy.PublicSourceRequirement
earlyYearsStrategyRequirement = Policy.requireAttributedSource EarlyYears.earlyYearsStrategy2024Attributed

qualityArea6Requirement : Policy.PublicSourceRequirement
qualityArea6Requirement = Policy.requireAttributedSource EarlyYears.qualityArea6Attributed

brownKimberRequirement : Policy.PublicSourceRequirement
brownKimberRequirement = Policy.requireAttributedSource EarlyYears.brownKimber2026Attributed

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
-- Full Alice provenance stays first-class rather than being reduced to the
-- Brown/Kimber row used by the latest early-years specialization.
------------------------------------------------------------------------

fullAliceCorpusRegistry : AliceSources.EducationCorpusSourceRegistry
fullAliceCorpusRegistry = AliceSources.canonicalEducationCorpusSourceRegistry

fullAliceCorpusLoom : Alice.AliceBrownCorpusLoom
fullAliceCorpusLoom = Alice.canonicalAliceBrownCorpusLoom

fullAliceCorpusSourceCountReading : String
fullAliceCorpusSourceCountReading = Alice.canonicalCorpusLoomSourceCountReading

sioDOIState : Source.DOIState
sioDOIState = Source.doiState SIO.sio2014Source

brownKimberDOIState : Source.DOIState
brownKimberDOIState = Source.doiState EarlyYears.brownKimber2026Attributed

earlyYearsStrategyDOIState : Source.DOIState
earlyYearsStrategyDOIState = Source.doiState EarlyYears.earlyYearsStrategy2024Attributed

qualityArea6DOIState : Source.DOIState
qualityArea6DOIState = Source.doiState EarlyYears.qualityArea6Attributed

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
  workingGroupSourceConformanceBoundary true true true true true true true false false false
