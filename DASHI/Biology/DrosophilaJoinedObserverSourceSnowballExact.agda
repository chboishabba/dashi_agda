module DASHI.Biology.DrosophilaJoinedObserverSourceSnowballExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Wikimedia.ScientificReferenceEntityAtlasExact as Ref
import DASHI.Ontology.DeweyQidCoverageQualityExact as Coverage

------------------------------------------------------------------------
-- DROSOPHILA JOINED-OBSERVER SOURCE SNOWBALL
--
-- Acquisition may proceed opportunistically across papers, datasets, atlas
-- resources, software, and local runtime receipts. Promotion remains ordered:
-- DOI/source object identity, same-object/data role, and empirical interpretation
-- must be paid separately. QID and Dewey coordinates are navigation metadata;
-- neither creates scientific authority.
------------------------------------------------------------------------

data SourceRole : Set where
  functionalImagingPrimary : SourceRole
  registrationMethodPrimary : SourceRole
  anatomicalTemplatePrimary : SourceRole
  atlasResourcePrimary : SourceRole
  structuralConnectomePrimary : SourceRole
  localRuntimeReceipt : SourceRole

data PublicationState : Set where
  peerReviewedVersionOfRecord : PublicationState
  preprintPredecessor : PublicationState
  resourceOrDataset : PublicationState
  localGeneratedArtifact : PublicationState

record SnowballSourceReceipt : Set where
  constructor snowball-source-receipt
  field
    canonicalTitle : String
    leadAttribution : String
    sourceRole : SourceRole
    publicationState : PublicationState
    primaryIdentifier : String
    predecessorIdentifier : String
    sourceDate : String
    deweyParent : String
    deweyNarrowCandidate : String
    qidEntity : Ref.ScientificReferenceEntity
    qidLookupState : String
    formalisationRelationship : String

open SnowballSourceReceipt public

biologyParent : String
biologyParent = "570.000"

neuroscienceNarrowCandidate : String
neuroscienceNarrowCandidate = "612.8"

gautheyWholeBrainImaging : SnowballSourceReceipt
gautheyWholeBrainImaging =
  snowball-source-receipt
    "High-speed whole-brain imaging in Drosophila"
    "Wayan Gauthey; Albert Lin; Osama M. Ahmed; Andrew M. Leifer; Mala Murthy; Stephan Y. Thiberge"
    functionalImagingPrimary
    peerReviewedVersionOfRecord
    "doi:10.1038/s41467-026-72437-1"
    "doi:10.1101/2025.06.18.660371"
    "2026-04-28 Nature Communications publication; version of record updated 2026-07-03"
    biologyParent neuroscienceNarrowCandidate
    (Ref.unresolved
      "High-speed whole-brain imaging in Drosophila"
      Ref.publicationEntity
      "No trustworthy publication QID resolved in 2026-09-11 title/DOI search; keep unresolved rather than infer from author/species entities")
    "publication QID unresolved as of 2026-09-11"
    "Primary authority for the functional-imaging acquisition/stimulus method used by the Gauthey LBM lane; does not establish MaleCNS neuron identity."

bifrostRegistration : SnowballSourceReceipt
bifrostRegistration =
  snowball-source-receipt
    "BIFROST: A method for registering diverse imaging datasets of the Drosophila brain"
    "Bella E. Brezovec; Andrew B. Berger; Yukun A. Hao; Albert Lin; Osama M. Ahmed; Diego A. Pacheco; Stephan Y. Thiberge; Mala Murthy; Thomas R. Clandinin"
    registrationMethodPrimary
    peerReviewedVersionOfRecord
    "doi:10.1073/pnas.2322687121"
    "doi:10.1101/2023.06.09.544408"
    "2024-11-14 online; PNAS 2024-11-19"
    biologyParent neuroscienceNarrowCandidate
    (Ref.unresolved
      "BIFROST: A method for registering diverse imaging datasets of the Drosophila brain"
      Ref.publicationEntity
      "No trustworthy publication QID resolved in 2026-09-11 title/DOI search")
    "publication QID unresolved as of 2026-09-11"
    "Primary method authority for cross-modality registration into a common Drosophila anatomical space; registration precision does not imply trace-to-neuron identity."

jrc2018Template : SnowballSourceReceipt
jrc2018Template =
  snowball-source-receipt
    "An unbiased template of the Drosophila brain and ventral nerve cord"
    "John A. Bogovic; Hideo Otsuna; Larissa Heinrich; Masayoshi Ito; Jennifer Jeter; Geoffrey Meissner; Aljoscha Nern; Jennifer Colonell; Oz Malkesman; Kei Ito; Stephan Saalfeld"
    anatomicalTemplatePrimary
    peerReviewedVersionOfRecord
    "doi:10.1371/journal.pone.0236495"
    "doi:10.1101/376384"
    "2020-12-31 PLOS ONE"
    biologyParent neuroscienceNarrowCandidate
    (Ref.unresolved
      "An unbiased template of the Drosophila brain and ventral nerve cord"
      Ref.publicationEntity
      "No trustworthy publication QID resolved in 2026-09-11 title/DOI search")
    "publication QID unresolved as of 2026-09-11"
    "Primary publication identity for the JRC2018 template family; the 46 VFB painted domains are a downstream atlas resource layered onto this template."

virtualFlyBrainAtlas : SnowballSourceReceipt
virtualFlyBrainAtlas =
  snowball-source-receipt
    "Virtual Fly Brain—An interactive atlas of the Drosophila nervous system"
    "Robert Court; Marta Costa; Clare Pilgrim; Gillian Millburn; Alex Holmes; Alex McLachlan; Aoife Larkin; et al."
    atlasResourcePrimary
    peerReviewedVersionOfRecord
    "doi:10.3389/fphys.2023.1076533"
    "not-applicable"
    "2023 Frontiers in Physiology"
    biologyParent neuroscienceNarrowCandidate
    (Ref.unresolved
      "Virtual Fly Brain—An interactive atlas of the Drosophila nervous system"
      Ref.publicationEntity
      "No trustworthy publication QID resolved in 2026-09-11 title/DOI search")
    "publication QID unresolved as of 2026-09-11"
    "Primary publication for VFB as an atlas/integration resource; current VFB documentation reports 46 painted JRC2018Unisex domains."

maleCnsConnectome : SnowballSourceReceipt
maleCnsConnectome =
  snowball-source-receipt
    "Sexual dimorphism in the complete Drosophila male central nervous system connectome"
    "Stuart Berg; Isabella R. Beckett; Marta Costa; Philipp Schlegel; Michal Januszewski; Elizabeth C. Marin; et al."
    structuralConnectomePrimary
    peerReviewedVersionOfRecord
    "doi:10.1016/j.cell.2026.08.015"
    "doi:10.1101/2025.10.09.680999"
    "2026-09-03 Cell 189(18):5504-5526.e15"
    biologyParent neuroscienceNarrowCandidate
    (Ref.unresolved
      "Sexual dimorphism in the complete Drosophila male central nervous system connectome"
      Ref.publicationEntity
      "No trustworthy publication QID resolved in 2026-09-11 title/DOI search")
    "publication QID unresolved as of 2026-09-11"
    "Primary structural-connectome publication for the MaleCNS v1.0 lane; structural connectivity does not by itself establish functional activation or causal necessity."

record JoinedObserverRuntimeReceipt : Set where
  constructor joined-observer-runtime-receipt
  field
    repository : String
    branch : String
    runtimeCommit : String
    artifactPath : String
    trialIdentity : String
    regionCount : Nat
    fibreCount : Nat
    nullCountPerFamily : Nat
    rawSoftResidual : String
    overlapControlledResidual : String
    stimulusControlledResidual : String
    joinedResidual : String
    strengthNullP : String
    labelNullP : String
    testReceipt : String
    interpretation : String

open JoinedObserverRuntimeReceipt public

currentJoinedObserverRuntime : JoinedObserverRuntimeReceipt
currentJoinedObserverRuntime =
  joined-observer-runtime-receipt
    "github.com/chboishabba/dashiBRAIN"
    "agent/malecns-real-benchmark-tranche"
    "c2dd30118c45521c2eeebd407f8d421d9c5b88b3"
    "data/gauthey_lbm/jrc2018_regions_a2_r5/malecns_joined_observer_ndim.json"
    "04032024_6f_a2_r5"
    26
    8
    100
    "0.1485"
    "0.1360"
    "0.1496"
    "0.1364"
    "0.3366"
    "0.8317"
    "166/166 pytest suite passing after joined-observer run; user-supplied local execution receipt 2026-09-11"
    "Joined controls retain held-out predictivity, but strength-preserving and co-permuted label nulls are not rejected. Pair-specific wiring and population-level mechanism remain unpaid."

record SourceSnowballBoundary : Set where
  constructor source-snowball-boundary
  field
    acquisitionMayProceedOutOfDependencyOrder : Bool
    promotionMaySkipSameObjectIdentity : Bool
    versionOfRecordSupersedesPreprintAsPrimaryPublicationIdentity : Bool
    predecessorDoiRemainsProvenance : Bool
    qidMayRemainExplicitlyUnresolved : Bool
    qidCreatesScientificAuthority : Bool
    deweyCreatesScientificAuthority : Bool
    doiCreatesProof : Bool
    localRuntimeReceiptBecomesExternalPrimarySource : Bool
    structuralConnectomeImpliesFunctionalMechanism : Bool

canonicalSourceSnowballBoundary : SourceSnowballBoundary
canonicalSourceSnowballBoundary =
  source-snowball-boundary
    true false true true true false false false false false

coverageBoundaryAnchor : Coverage.CoverageQualityBoundary
coverageBoundaryAnchor = Coverage.canonicalCoverageQualityBoundary

data UnresolvedQidMayBeInventedFromTitleSimilarity : Set where
unresolvedQidCannotBeInvented : UnresolvedQidMayBeInventedFromTitleSimilarity → ⊥
unresolvedQidCannotBeInvented ()
