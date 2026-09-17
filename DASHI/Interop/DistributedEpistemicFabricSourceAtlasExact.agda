module DASHI.Interop.DistributedEpistemicFabricSourceAtlasExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution

------------------------------------------------------------------------
-- DISTRIBUTED EPISTEMIC FABRIC SOURCE / CONTRIBUTION ATTRIBUTION ATLAS
--
-- This owner is deliberately about provenance, not legal title.
--
-- JMD / meta-introspector owns the observed source repositories and the
-- source-level architecture/implementation artefacts actually present there.
-- Johl Brown is attributed here for the 2026-09-17 discussion-origin
-- architecture proposal joining replicated logs/projections, situated access,
-- SOLFUNMEME settlement, and the Agda : SLR : Lean/wiki-prover braid.
-- External projects retain ownership of their own technology implementations
-- and documentation.  DASHI owns the finite typed reconstruction and the
-- non-collapse theorems introduced in this repository.
--
-- Attribution here does NOT adjudicate copyright ownership, authorship disputes,
-- licence compatibility, or legal title.  Repository licence observations are
-- exact observations at the inspected root/ref only.
------------------------------------------------------------------------

data ContributionOrigin : Set where
  jmdMetaIntrospectorOrigin : ContributionOrigin
  johlBrownOrigin : ContributionOrigin
  externalTechnologyOrigin : ContributionOrigin
  dashiSynthesisOrigin : ContributionOrigin

record ContributionAttribution : Set where
  constructor contributionAttribution
  field
    contributionLabel : String
    contributionOrigin : ContributionOrigin
    sourceCoordinate : String
    sourceBoundary : String
    legalTitleAdjudicated : Bool
    legalTitleAdjudicatedIsFalse : legalTitleAdjudicated ≡ false

open ContributionAttribution public

jmdRepositoryContribution : ContributionAttribution
jmdRepositoryContribution =
  contributionAttribution
    "JMD / meta-introspector repository architecture and implementation witnesses"
    jmdMetaIntrospectorOrigin
    "https://github.com/meta-introspector"
    "Only source-level repository artefacts actually observed in the named JMD/meta-introspector repositories are attributed here; DASHI bridge theorems are not reassigned to JMD."
    false
    refl

johlDiscussionContribution : ContributionAttribution
johlDiscussionContribution =
  contributionAttribution
    "2026-09-17 distributed epistemic fabric / situated-access integration proposal"
    johlBrownOrigin
    "DASHI design discussion 2026-09-17"
    "Discussion-origin attribution for the proposed architectural composition and access-path framing; this record does not adjudicate legal ownership or exclusive priority."
    false
    refl

externalTechnologyContribution : ContributionAttribution
externalTechnologyContribution =
  contributionAttribution
    "external content-addressed, replicated-log, bulk-distribution and settlement precedents"
    externalTechnologyOrigin
    "OrbitDB / IPFS / BitTorrent / Solana public project surfaces"
    "External projects are architecture/implementation precedents only; no external project owns the DASHI reconstruction or its finite firewalls."
    false
    refl

dashiFormalContribution : ContributionAttribution
dashiFormalContribution =
  contributionAttribution
    "typed plane separation, receipt ABI, situated-access carriers and non-collapse firewalls"
    dashiSynthesisOrigin
    "chboishabba/dashi_agda"
    "Repository-native DASHI synthesis over the attributed source/discussion coordinates."
    false
    refl

------------------------------------------------------------------------
-- Licence observations.
------------------------------------------------------------------------

data LicenseObservation : Set where
  mitLicenseObserved : LicenseObservation
  agpl3LicenseObserved : LicenseObservation
  licenseNotObservedAtInspectedRoot : LicenseObservation

record RepositoryLicenseObservation : Set where
  constructor repositoryLicenseObservation
  field
    repositoryURL : String
    inspectedRef : String
    inspectedDate : String
    observedLicense : LicenseObservation
    observationNote : String
    observationCreatesReuseRight : Bool
    observationCreatesReuseRightIsFalse : observationCreatesReuseRight ≡ false
    missingLicenseDeterminesPermission : Bool
    missingLicenseDeterminesPermissionIsFalse : missingLicenseDeterminesPermission ≡ false

open RepositoryLicenseObservation public

erdfaPublishLicense : RepositoryLicenseObservation
erdfaPublishLicense =
  repositoryLicenseObservation
    "https://github.com/meta-introspector/erdfa-publish-rs"
    "main (head observed 2f6dc751781164385ae3d72a4d934d3d6a7b0d8d)"
    "2026-09-17"
    mitLicenseObserved
    "Root LICENSE observed: MIT License; copyright (c) 2026 meta-introspector."
    false refl false refl

solfunmemeDioxusLicense : RepositoryLicenseObservation
solfunmemeDioxusLicense =
  repositoryLicenseObservation
    "https://github.com/meta-introspector/solfunmeme-dioxus"
    "main"
    "2026-09-17"
    agpl3LicenseObserved
    "Root LICENSE observed: GNU Affero General Public License version 3."
    false refl false refl

zosServerLicense : RepositoryLicenseObservation
zosServerLicense =
  repositoryLicenseObservation
    "https://github.com/meta-introspector/zos-server"
    "main"
    "2026-09-17"
    agpl3LicenseObserved
    "Root LICENSE observed: GNU Affero General Public License version 3."
    false refl false refl

metaMemeLicense : RepositoryLicenseObservation
metaMemeLicense =
  repositoryLicenseObservation
    "https://github.com/meta-introspector/meta-meme"
    "main"
    "2026-09-17"
    mitLicenseObserved
    "Root LICENSE observed: MIT License; copyright (c) 2023, James Michael DuPont."
    false refl false refl

ipfsDaslLicense : RepositoryLicenseObservation
ipfsDaslLicense =
  repositoryLicenseObservation
    "https://github.com/meta-introspector/ipfs-dasl"
    "master"
    "2026-09-17"
    licenseNotObservedAtInspectedRoot
    "No root LICENSE file was observed at the inspected default head. This is an observation about that root, not a legal conclusion about permission or prohibition."
    false refl false refl

meshSyncLicense : RepositoryLicenseObservation
meshSyncLicense =
  repositoryLicenseObservation
    "https://github.com/meta-introspector/mesh-sync-rs"
    "main"
    "2026-09-17"
    licenseNotObservedAtInspectedRoot
    "No root LICENSE file was observed at the inspected default head. This is an observation about that root, not a legal conclusion about permission or prohibition."
    false refl false refl

------------------------------------------------------------------------
-- Recoverable source/project coordinates.
------------------------------------------------------------------------

jmdErdfaSource : Attribution.AttributedSource
jmdErdfaSource =
  Attribution.mkNoDOISource
    "meta-introspector / JMD project"
    "erdfa-publish-rs"
    "GitHub software repository"
    "2026"
    "https://github.com/meta-introspector/erdfa-publish-rs"
    (Attribution.namedSourceKind "software repository")
    "JMD/meta-introspector semantic publication / content-addressed shard implementation witness; source architecture only, not DASHI theorem authority."
    Attribution.publicAttribution

jmdIpfsDaslSource : Attribution.AttributedSource
jmdIpfsDaslSource =
  Attribution.mkNoDOISource
    "meta-introspector / JMD project"
    "ipfs-dasl"
    "GitHub software repository"
    "2026"
    "https://github.com/meta-introspector/ipfs-dasl"
    (Attribution.namedSourceKind "software repository")
    "JMD/meta-introspector canonical serialization/conformance and content-addressed representation witness."
    Attribution.publicAttribution

jmdMeshSyncSource : Attribution.AttributedSource
jmdMeshSyncSource =
  Attribution.mkNoDOISource
    "meta-introspector / JMD project"
    "mesh-sync-rs"
    "GitHub software repository"
    "2026"
    "https://github.com/meta-introspector/mesh-sync-rs"
    (Attribution.namedSourceKind "software repository")
    "JMD/meta-introspector transport/synchronization implementation witness; transport does not create semantic authority."
    Attribution.publicAttribution

jmdZosSource : Attribution.AttributedSource
jmdZosSource =
  Attribution.mkNoDOISource
    "meta-introspector / JMD project"
    "zos-server"
    "GitHub software repository"
    "2026"
    "https://github.com/meta-introspector/zos-server"
    (Attribution.namedSourceKind "software repository")
    "JMD/meta-introspector reconciliation/runtime implementation witness; reconciliation does not create canonical semantic identity."
    Attribution.publicAttribution

jmdSolfunmemeSource : Attribution.AttributedSource
jmdSolfunmemeSource =
  Attribution.mkNoDOISource
    "meta-introspector / JMD project"
    "solfunmeme-dioxus"
    "GitHub software repository"
    "2026"
    "https://github.com/meta-introspector/solfunmeme-dioxus"
    (Attribution.namedSourceKind "software repository")
    "JMD/meta-introspector SOLFUNMEME application/value/governance implementation witness; settlement is not semantic truth."
    Attribution.publicAttribution

jmdMetaMemeSource : Attribution.AttributedSource
jmdMetaMemeSource =
  Attribution.mkNoDOISource
    "James Michael DuPont / meta-introspector"
    "meta-meme"
    "GitHub software repository"
    "2023"
    "https://github.com/meta-introspector/meta-meme"
    (Attribution.namedSourceKind "software repository")
    "JMD/meta-introspector MetaMeme source coordinate; repository source does not transfer ownership of DASHI bridge mathematics."
    Attribution.publicAttribution

orbitDBSource : Attribution.AttributedSource
orbitDBSource =
  Attribution.mkNoDOISource
    "OrbitDB contributors"
    "OrbitDB"
    "GitHub software project"
    ""
    "https://github.com/orbitdb/orbitdb"
    (Attribution.namedSourceKind "external software project")
    "External precedent for authenticated replicated log/database projections over content-addressed peer-to-peer storage; no claim that DASHI/SLR currently deploys OrbitDB."
    Attribution.publicAttribution

ipfsSource : Attribution.AttributedSource
ipfsSource =
  Attribution.mkNoDOISource
    "IPFS / Protocol Labs ecosystem contributors"
    "InterPlanetary File System (IPFS)"
    "public software/documentation project"
    ""
    "https://ipfs.tech/"
    (Attribution.namedSourceKind "external software project")
    "External content-addressed object-network precedent; CID identity does not create semantic authority."
    Attribution.publicAttribution

bitTorrentSource : Attribution.AttributedSource
bitTorrentSource =
  Attribution.mkNoDOISource
    "BitTorrent protocol ecosystem"
    "BitTorrent"
    "public protocol/software ecosystem"
    ""
    "https://www.bittorrent.org/"
    (Attribution.namedSourceKind "external protocol project")
    "External bulk immutable byte-distribution comparator; swarm availability is not provenance or semantic truth."
    Attribution.publicAttribution

solanaSource : Attribution.AttributedSource
solanaSource =
  Attribution.mkNoDOISource
    "Solana project contributors"
    "Solana"
    "public blockchain/software project"
    ""
    "https://solana.com/"
    (Attribution.namedSourceKind "external software project")
    "External settlement/consensus precedent only; chain consensus does not create epistemic truth."
    Attribution.publicAttribution

distributedEpistemicSourceAtlas : Attribution.AttributedSourceAtlas
distributedEpistemicSourceAtlas =
  Attribution.mkSourceAtlas
    "distributed epistemic fabric source atlas"
    "DASHI.Interop.DistributedEpistemicFabricSourceAtlasExact"
    (jmdErdfaSource ∷ jmdIpfsDaslSource ∷ jmdMeshSyncSource ∷ jmdZosSource ∷
     jmdSolfunmemeSource ∷ jmdMetaMemeSource ∷ orbitDBSource ∷ ipfsSource ∷
     bitTorrentSource ∷ solanaSource ∷ [])
    "Source/project coordinates for the distributed epistemic fabric formalisation; repository/project observations remain distinct from Johl Brown discussion-origin architecture and DASHI theorem synthesis."

attributionRule : String
attributionRule =
  "JMD/meta-introspector repositories retain attribution for observed source artefacts and implementation architecture; Johl Brown is attributed for the 2026-09-17 discussion-origin composition/access-path proposal; external projects retain their own technology claims; DASHI owns the typed reconstruction and finite firewalls. Attribution does not adjudicate legal title, source identity does not import proof, and a licence observation does not itself create semantic authority or a new reuse right."

------------------------------------------------------------------------
-- Attribution / licence firewalls.
------------------------------------------------------------------------

data AttributionCreatesLegalTitle : Set where
data LicenseObservationCreatesSemanticAuthority : Set where
data MissingRootLicenseDeterminesPermission : Set where
data JMDSourceOwnsDASHIBridgeTheorem : Set where
data DiscussionAttributionCreatesExclusivePriority : Set where

attributionDoesNotAdjudicateLegalTitle : AttributionCreatesLegalTitle → ⊥
attributionDoesNotAdjudicateLegalTitle ()

licenseObservationIsNotSemanticAuthority : LicenseObservationCreatesSemanticAuthority → ⊥
licenseObservationIsNotSemanticAuthority ()

missingRootLicenseDoesNotDeterminePermission : MissingRootLicenseDeterminesPermission → ⊥
missingRootLicenseDoesNotDeterminePermission ()

jmdSourceDoesNotOwnDASHIBridgeTheorem : JMDSourceOwnsDASHIBridgeTheorem → ⊥
jmdSourceDoesNotOwnDASHIBridgeTheorem ()

discussionAttributionDoesNotCreateExclusivePriority : DiscussionAttributionCreatesExclusivePriority → ⊥
discussionAttributionDoesNotCreateExclusivePriority ()
