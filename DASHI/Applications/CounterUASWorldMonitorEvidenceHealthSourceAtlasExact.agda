module DASHI.Applications.CounterUASWorldMonitorEvidenceHealthSourceAtlasExact where

open import DASHI.Core.Prelude

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball

------------------------------------------------------------------------
-- WORLDMONITOR IMPLEMENTATION-PRECEDENT SOURCE ATLAS
--
-- These are commit-pinned software/documentation sources from
-- chboishabba/worldmonitor. They pay only implementation-precedent coordinates:
-- explicit freshness/health state, intelligence-gap visibility, temporal
-- baseline context, and multi-source corroboration design. They do not import
-- proofs, validate counter-UAS products, establish emitter identity, or create
-- operational/legal authority.
------------------------------------------------------------------------

worldMonitorCommit : String
worldMonitorCommit = "7142fb8d806fbfe238b2918f4e22ba8ceeac06af"

worldMonitorArchitecture : Source.AttributedSource
worldMonitorArchitecture =
  Source.mkNoDOISource
    "World Monitor contributors"
    "ARCHITECTURE.md"
    "chboishabba/worldmonitor software repository, commit 7142fb8d806fbfe238b2918f4e22ba8ceeac06af"
    "2026"
    "https://github.com/chboishabba/worldmonitor/blob/7142fb8d806fbfe238b2918f4e22ba8ceeac06af/ARCHITECTURE.md"
    (Source.namedSourceKind "software repository documentation")
    "implementation precedent for seed metadata, explicit freshness thresholds, fallback cascades, health monitoring, temporal baselines, and multi-source data aggregation; not a formal proof or counter-UAS validation source"
    Source.publicAttribution

worldMonitorDesignPhilosophy : Source.AttributedSource
worldMonitorDesignPhilosophy =
  Source.mkNoDOISource
    "World Monitor contributors"
    "Design Philosophy"
    "chboishabba/worldmonitor software repository, commit 7142fb8d806fbfe238b2918f4e22ba8ceeac06af"
    "2026"
    "https://github.com/chboishabba/worldmonitor/blob/7142fb8d806fbfe238b2918f4e22ba8ceeac06af/docs/architecture.mdx"
    (Source.namedSourceKind "software repository documentation")
    "implementation precedent for explicit intelligence gaps, source-credibility metadata, multi-signal corroboration, and baseline-aware alerting; agreement language is not imported as a proof of independent genealogy"
    Source.publicAttribution

worldMonitorHealthEndpoint : Source.AttributedSource
worldMonitorHealthEndpoint =
  Source.mkNoDOISource
    "World Monitor contributors"
    "api/health.js"
    "chboishabba/worldmonitor software repository, commit 7142fb8d806fbfe238b2918f4e22ba8ceeac06af"
    "2026"
    "https://github.com/chboishabba/worldmonitor/blob/7142fb8d806fbfe238b2918f4e22ba8ceeac06af/api/health.js"
    (Source.namedSourceKind "software implementation")
    "implementation precedent for per-key freshness thresholds, on-demand/empty-data exceptions, cascade fallback groups, and explicit source-health state; missing or empty data is context-indexed rather than automatically interpreted as phenomenon absence"
    Source.publicAttribution

worldMonitorEvidenceHealthSources : List Source.AttributedSource
worldMonitorEvidenceHealthSources =
  worldMonitorArchitecture ∷
  worldMonitorDesignPhilosophy ∷
  worldMonitorHealthEndpoint ∷
  []

worldMonitorEvidenceHealthSourceAtlas : Source.AttributedSourceAtlas
worldMonitorEvidenceHealthSourceAtlas =
  Source.mkSourceAtlas
    "WorldMonitor evidence-health implementation precedents"
    "DASHI.Applications.CounterUASWorldMonitorEvidenceHealthSourceAtlasExact"
    worldMonitorEvidenceHealthSources
    "commit-pinned implementation precedents for freshness, gaps, baselines, fallback state and multi-source corroboration; repository sources do not import proof, establish independent genealogy, identify an emitter, validate DroneShield, or create operational/legal authority"

worldMonitorEvidenceHealthSourceAtlasCreatesAuthority : Bool
worldMonitorEvidenceHealthSourceAtlasCreatesAuthority =
  Source.atlasCreatesAuthority worldMonitorEvidenceHealthSourceAtlas

worldMonitorEvidenceHealthSourceAtlasCreatesAuthorityIsFalse :
  worldMonitorEvidenceHealthSourceAtlasCreatesAuthority ≡ false
worldMonitorEvidenceHealthSourceAtlasCreatesAuthorityIsFalse =
  Source.atlasCreatesAuthorityIsFalse worldMonitorEvidenceHealthSourceAtlas

worldMonitorArchitectureSnowballReceipt :
  Snowball.SourceRoleSnowballReceipt worldMonitorArchitecture
worldMonitorArchitectureSnowballReceipt =
  Snowball.canonicalSourceRoleSnowballReceipt worldMonitorArchitecture

worldMonitorDesignPhilosophySnowballReceipt :
  Snowball.SourceRoleSnowballReceipt worldMonitorDesignPhilosophy
worldMonitorDesignPhilosophySnowballReceipt =
  Snowball.canonicalSourceRoleSnowballReceipt worldMonitorDesignPhilosophy

worldMonitorHealthEndpointSnowballReceipt :
  Snowball.SourceRoleSnowballReceipt worldMonitorHealthEndpoint
worldMonitorHealthEndpointSnowballReceipt =
  Snowball.canonicalSourceRoleSnowballReceipt worldMonitorHealthEndpoint

record WorldMonitorEvidenceHealthAttributionBoundary : Set where
  constructor worldMonitorEvidenceHealthAttributionBoundary
  field
    implementationPatternEqualsImportedProof : Bool
    implementationPatternEqualsImportedProofIsFalse :
      implementationPatternEqualsImportedProof ≡ false
    repositoryPatternValidatesCounterUASProduct : Bool
    repositoryPatternValidatesCounterUASProductIsFalse :
      repositoryPatternValidatesCounterUASProduct ≡ false
    multiSourceDesignProvesIndependentGenealogy : Bool
    multiSourceDesignProvesIndependentGenealogyIsFalse :
      multiSourceDesignProvesIndependentGenealogy ≡ false

canonicalWorldMonitorEvidenceHealthAttributionBoundary :
  WorldMonitorEvidenceHealthAttributionBoundary
canonicalWorldMonitorEvidenceHealthAttributionBoundary =
  worldMonitorEvidenceHealthAttributionBoundary
    false refl
    false refl
    false refl
