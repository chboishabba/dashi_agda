module DASHI.Interop.SensibLawFederatedZOSAcquisitionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- FEDERATED ZOS / ERDFA / IPFS ACQUISITION BOUNDARY
--
-- Runtime owner:
--   chboishabba/SensibLaw :: src/pnf/federated_zos_acquisition.py
-- Existing identity/publication owners:
--   src/pnf/sync_identity.py
--   src/pnf/erdfa_export.py
--
-- Federation distributes storage, routing, parsing and public-ontology
-- candidate production.  It does not distribute semantic authority merely
-- because bytes or a CID are available remotely.
------------------------------------------------------------------------

data CorpusPrivacy : Set where
  publicCorpus restrictedCorpus localOnlyCorpus : CorpusPrivacy

data RemoteCapability : Set where
  storageCapability computeCapability discoveryCapability ontologyCapability : RemoteCapability

data SourceClass : Set where
  primaryAuthority secondarySource measurementSource comparatorSource publicOntology : SourceClass

data ConsumerClass : Set where
  obsidianConsumer legalConsumer medicalConsumer publicResearchConsumer : ConsumerClass

record AcquisitionPolicy : Set where
  constructor acquisitionPolicy
  field
    consumer : ConsumerClass
    privacy : CorpusPrivacy
    allowRemoteStorage : Bool
    allowRemoteCompute : Bool
    allowRemoteDiscovery : Bool
    allowPublicOntologyCandidates : Bool
    advertisePrivateCorpus : Bool
    maxDepth : Nat

open AcquisitionPolicy public

legalStrictPolicy : AcquisitionPolicy
legalStrictPolicy = acquisitionPolicy legalConsumer restrictedCorpus false false true true false 4

medicalStrictPolicy : AcquisitionPolicy
medicalStrictPolicy = acquisitionPolicy medicalConsumer restrictedCorpus false false true true false 3

obsidianLocalPolicy : AcquisitionPolicy
obsidianLocalPolicy = acquisitionPolicy obsidianConsumer localOnlyCorpus false false true true false 2

publicResearchPolicy : AcquisitionPolicy
publicResearchPolicy = acquisitionPolicy publicResearchConsumer publicCorpus true true true true false 8

record FederatedContentBoundary : Set where
  constructor federatedContentBoundary
  field
    zosCanonicalIdentityRetained : Bool
    erdfaRetainsReplayLocatorSet : Bool
    ipfsMayBeReplayLocator : Bool
    contentDigestSharedAcrossMirrors : Bool
    contentIdentityCreatesSemanticAuthority : Bool
    mirrorAvailabilityCreatesClaimTruth : Bool
    mirrorAvailabilityCreatesEvidencePayment : Bool

open FederatedContentBoundary public

canonicalFederatedContentBoundary : FederatedContentBoundary
canonicalFederatedContentBoundary =
  federatedContentBoundary true true true true false false false

record FederatedPrivacyBoundary : Set where
  constructor federatedPrivacyBoundary
  field
    storageComputeRoutingMayBeDifferentPeers : Bool
    restrictedCorpusBytesMayLeaveLocalNode : Bool
    restrictedCorpusIdentityAdvertised : Bool
    restrictedDiscoveryMayUseResidualOnly : Bool
    publicOntologyReceivesPrivateCorpus : Bool

open FederatedPrivacyBoundary public

canonicalFederatedPrivacyBoundary : FederatedPrivacyBoundary
canonicalFederatedPrivacyBoundary =
  federatedPrivacyBoundary true false false true false

record ParallelOntologyBoundary : Set where
  constructor parallelOntologyBoundary
  field
    wikidataCandidateProducer : Bool
    dbpediaCandidateProducer : Bool
    medicalOntologyCandidateProducer : Bool
    oeisCandidateProducer : Bool
    ontologyCandidateCreatesTruth : Bool
    ontologyCandidateAllowsOntologyTransplant : Bool

open ParallelOntologyBoundary public

canonicalParallelOntologyBoundary : ParallelOntologyBoundary
canonicalParallelOntologyBoundary =
  parallelOntologyBoundary true true true true false false

record MaboFederatedResidualBoundary : Set where
  constructor maboFederatedResidualBoundary
  field
    exactCommonGroundGeneratesSearchWork : Bool
    liveContradictionMayGeneratePrimaryAuthorityRequest : Bool
    primaryAuthorityRequestCreatesFact : Bool
    primaryAuthorityRequestPromotesTruth : Bool
    sourceRoleReviewStillRequired : Bool

open MaboFederatedResidualBoundary public

canonicalMaboFederatedResidualBoundary : MaboFederatedResidualBoundary
canonicalMaboFederatedResidualBoundary =
  maboFederatedResidualBoundary false true false false true

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data CIDCreatesSemanticAuthority : Set where
data MirrorCountCreatesTruth : Set where
data RemoteAvailabilityPaysEvidence : Set where
data FederatedCapabilityImpliesDisclosurePermission : Set where
data PublicOntologyCreatesClaimTruth : Set where
data PublicOntologyMayTransplantOntology : Set where
data ExactMaboCommonGroundRequiresFederatedSearch : Set where

aCIDIsNotSemanticAuthority : CIDCreatesSemanticAuthority → ⊥
aCIDIsNotSemanticAuthority ()

mirrorCountIsNotTruth : MirrorCountCreatesTruth → ⊥
mirrorCountIsNotTruth ()

remoteAvailabilityIsNotEvidencePayment : RemoteAvailabilityPaysEvidence → ⊥
remoteAvailabilityIsNotEvidencePayment ()

capabilityDoesNotGrantDisclosurePermission : FederatedCapabilityImpliesDisclosurePermission → ⊥
capabilityDoesNotGrantDisclosurePermission ()

publicOntologyCandidateIsNotClaimTruth : PublicOntologyCreatesClaimTruth → ⊥
publicOntologyCandidateIsNotClaimTruth ()

publicOntologyDoesNotAuthorizeOntologyTransplant : PublicOntologyMayTransplantOntology → ⊥
publicOntologyDoesNotAuthorizeOntologyTransplant ()

maboExactCommonGroundIsZeroFederatedWork : ExactMaboCommonGroundRequiresFederatedSearch → ⊥
maboExactCommonGroundIsZeroFederatedWork ()
