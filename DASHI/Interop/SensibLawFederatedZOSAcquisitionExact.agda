module DASHI.Interop.SensibLawFederatedZOSAcquisitionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- FEDERATED ZOS / ERDFA / IPFS ACQUISITION BOUNDARY
--
-- Runtime owners:
--   chboishabba/SensibLaw :: src/pnf/federated_zos_acquisition.py
--   chboishabba/SensibLaw :: src/pnf/progressive_acquisition_depth.py
-- Existing identity/publication/execution owners:
--   src/pnf/sync_identity.py
--   src/pnf/erdfa_export.py
--   src/storage/postgres/distributed_semantic_execution.py
------------------------------------------------------------------------

data CorpusPrivacy : Set where
  publicCorpus restrictedCorpus localOnlyCorpus : CorpusPrivacy

data RemoteCapability : Set where
  storageCapability computeCapability discoveryCapability ontologyCapability : RemoteCapability

data SourceClass : Set where
  primaryAuthority secondarySource measurementSource comparatorSource publicOntology : SourceClass

data ConsumerClass : Set where
  obsidianConsumer legalConsumer medicalConsumer publicResearchConsumer : ConsumerClass

data AcquisitionDepth : Set where
  searchResultDepth abstractDepth fullSourceDepth : AcquisitionDepth

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

record DistributedComputeBoundary : Set where
  constructor distributedComputeBoundary
  field
    existingTypedPostgresWorkerReused : Bool
    stableInputRefIsExecutionIdentityOnly : Bool
    publicPolicyMayDispatchParseCompute : Bool
    legalRestrictedPolicyMayDispatchParseCompute : Bool
    medicalRestrictedPolicyMayDispatchParseCompute : Bool
    rejectedDispatchDisclosesPayload : Bool
    distributedExecutionCreatesSemanticAuthority : Bool

open DistributedComputeBoundary public

canonicalDistributedComputeBoundary : DistributedComputeBoundary
canonicalDistributedComputeBoundary =
  distributedComputeBoundary true true true false false false false

record ProgressiveDeepeningBoundary : Set where
  constructor progressiveDeepeningBoundary
  field
    searchResultPrecedesAbstract : Bool
    abstractPrecedesFullSource : Bool
    exactResidualMayDeepen : Bool
    exhaustedBudgetMayDeepen : Bool
    strictLegalPrimaryAuthorityNeedsFullSource : Bool
    strictLegalPrimaryAuthorityNeedsExactSpan : Bool
    fullSourceCreatesTruthWithoutReview : Bool
    fullSourceCreatesPaymentWithoutReview : Bool

open ProgressiveDeepeningBoundary public

canonicalProgressiveDeepeningBoundary : ProgressiveDeepeningBoundary
canonicalProgressiveDeepeningBoundary =
  progressiveDeepeningBoundary true true false false true true false false

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
data StableInputRefCreatesSemanticAuthority : Set where
data RestrictedComputeMayDisclosePayload : Set where
data SearchResultPaysPrimaryAuthority : Set where
data AbstractPaysPrimaryAuthority : Set where
data FullSourcePaysWithoutReview : Set where

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

stableInputIdentityIsNotSemanticAuthority : StableInputRefCreatesSemanticAuthority → ⊥
stableInputIdentityIsNotSemanticAuthority ()

restrictedComputeDisclosureForbidden : RestrictedComputeMayDisclosePayload → ⊥
restrictedComputeDisclosureForbidden ()

searchResultCannotPayPrimaryAuthority : SearchResultPaysPrimaryAuthority → ⊥
searchResultCannotPayPrimaryAuthority ()

abstractCannotPayPrimaryAuthority : AbstractPaysPrimaryAuthority → ⊥
abstractCannotPayPrimaryAuthority ()

fullSourceStillNeedsReviewForPayment : FullSourcePaysWithoutReview → ⊥
fullSourceStillNeedsReviewForPayment ()
