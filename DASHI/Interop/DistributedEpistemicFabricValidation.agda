module DASHI.Interop.DistributedEpistemicFabricValidation where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (false; true)
open import Data.Empty using (⊥)

import DASHI.Interop.DistributedEpistemicFabricSourceAtlasExact as Sources
import DASHI.Interop.DistributedEpistemicPlaneSeparationExact as Planes
import DASHI.Interop.DistributedProofProducerABIExact as Producer
import DASHI.Economics.SituatedInformationAccessFabricExact as Access

import DASHI.Interop.DistributedEvidenceHistoryProjectionExact as History
import DASHI.Interop.ImmutableEvidenceSupersessionExact as Supersession
import DASHI.Interop.ReplicationCapabilityNonCollapseExact as Replication

------------------------------------------------------------------------
-- Focused compile-time boundary checks.
------------------------------------------------------------------------

erdfaMITObserved :
  Sources.observedLicense Sources.erdfaPublishLicense ≡ Sources.mitLicenseObserved
erdfaMITObserved = refl

solfunmemeAGPLObserved :
  Sources.observedLicense Sources.solfunmemeDioxusLicense ≡ Sources.agpl3LicenseObserved
solfunmemeAGPLObserved = refl

ipfsDaslLicenseNotObservedAtRoot :
  Sources.observedLicense Sources.ipfsDaslLicense ≡ Sources.licenseNotObservedAtInspectedRoot
ipfsDaslLicenseNotObservedAtRoot = refl

meshSyncLicenseNotObservedAtRoot :
  Sources.observedLicense Sources.meshSyncLicense ≡ Sources.licenseNotObservedAtInspectedRoot
meshSyncLicenseNotObservedAtRoot = refl

orbitDbNotClaimedDeployed :
  Planes.orbitDbCurrentlyDeployed Planes.canonicalTechnologyRoleMap ≡ false
orbitDbNotClaimedDeployed = refl

solanaNotApplicationDatabase :
  Planes.solanaIsApplicationDatabase Planes.canonicalTechnologyRoleMap ≡ false
solanaNotApplicationDatabase = refl

settlementNotTruth :
  Planes.settlementCreatesTruth Planes.canonicalTechnologyRoleMap ≡ false
settlementNotTruth = refl

postgresProjectionNotGlobalTruth :
  Planes.postgresIsGlobalSemanticTruth Planes.canonicalTechnologyRoleMap ≡ false
postgresProjectionNotGlobalTruth = refl

thinkRoutesToLeanWikiProver :
  Producer.ownerOfAction Producer.thinkAction ≡ Producer.leanWikiProverProducer
thinkRoutesToLeanWikiProver = refl

lookRoutesToSLR :
  Producer.ownerOfAction Producer.lookAction ≡ Producer.slrAcquisitionProducer
lookRoutesToSLR = refl

reviewRoutesToHuman :
  Producer.ownerOfAction Producer.reviewAction ≡ Producer.humanReviewProducer
reviewRoutesToHuman = refl

publicPremiumSameObject :
  Access.underlyingInformation Access.publicPath ≡
  Access.underlyingInformation Access.premiumPath
publicPremiumSameObject = refl

premiumPathIsPremiumCapability :
  Access.premiumCapabilityPath Access.premiumPath ≡ true
premiumPathIsPremiumCapability = refl

publicPathRetainsCommonsLane :
  Access.publicCommonsPath Access.publicPath ≡ true
publicPathRetainsCommonsLane = refl

------------------------------------------------------------------------
-- Evidence/history/projection positive construction.
------------------------------------------------------------------------

derivedViewRetainsSource :
  History.sourceRetained History.exampleAuditableDerivedView ≡ true
derivedViewRetainsSource = refl

derivedViewRetainsObservation :
  History.observationRetained History.exampleAuditableDerivedView ≡ true
derivedViewRetainsObservation = refl

derivedViewRetainsHistory :
  History.historyRetained History.exampleAuditableDerivedView ≡ true
derivedViewRetainsHistory = refl

derivedViewDoesNotPromoteTruth :
  History.promotesClaimTruth History.exampleAuditableDerivedView ≡ false
derivedViewDoesNotPromoteTruth = refl

projectionIsConsumerRelative :
  History.consumerIdentity History.exampleProjection ≡ "consumer:example"
projectionIsConsumerRelative = refl

------------------------------------------------------------------------
-- Immutable supersession positive construction.
------------------------------------------------------------------------

supersessionKeepsEarlierSource :
  Supersession.earlierIdentityRetained Supersession.fixtureSupersessionReceipt ≡ true
supersessionKeepsEarlierSource = refl

supersessionKeepsLaterSource :
  Supersession.laterIdentityRetained Supersession.fixtureSupersessionReceipt ≡ true
supersessionKeepsLaterSource = refl

supersessionRelationExplicit :
  Supersession.relationExplicit Supersession.fixtureSupersessionReceipt ≡ true
supersessionRelationExplicit = refl

supersessionDoesNotPromoteTruth :
  Supersession.promotesTruth Supersession.fixtureSupersessionReceipt ≡ false
supersessionDoesNotPromoteTruth = refl

------------------------------------------------------------------------
-- Replication/capability taxonomy pins.
------------------------------------------------------------------------

bitTorrentIsBulkDistribution :
  Replication.primaryRole Replication.bitTorrentRole ≡ Replication.immutableBulkDistribution
bitTorrentIsBulkDistribution = refl

ipfsIsLinkedObjectGraph :
  Replication.primaryRole Replication.ipfsRole ≡ Replication.immutableLinkedObjectGraph
ipfsIsLinkedObjectGraph = refl

hypercoreAutobaseIsDeterministicMultiWriterProjection :
  Replication.primaryRole Replication.hypercoreAutobaseRole ≡ Replication.deterministicMultiWriterProjection
hypercoreAutobaseIsDeterministicMultiWriterProjection = refl

peerbitIsDistributedDiscoveryQuery :
  Replication.primaryRole Replication.peerbitRole ≡ Replication.distributedDiscoveryQuery
peerbitIsDistributedDiscoveryQuery = refl

automergeYjsIsSemanticCRDTState :
  Replication.primaryRole Replication.automergeYjsRole ≡ Replication.semanticCRDTState
automergeYjsIsSemanticCRDTState = refl

localDatabaseIsMaterialisation :
  Replication.primaryRole Replication.localDatabaseRole ≡ Replication.localQueryMaterialisation
localDatabaseIsMaterialisation = refl

------------------------------------------------------------------------
-- The following theorem references pin the non-collapse API itself.  If a
-- future refactor removes one of these authority boundaries the focused root
-- stops typechecking rather than silently weakening the architecture.
------------------------------------------------------------------------

cidFirewall : Planes.CIDCreatesAuthority → ⊥
cidFirewall = Planes.cidIsNotAuthority

settlementFirewall : Planes.SettlementCreatesEpistemicTruth → ⊥
settlementFirewall = Planes.settlementIsNotEpistemicTruth

proofPromotionFirewall : Producer.ProofReceiptCreatesPromotion → ⊥
proofPromotionFirewall = Producer.proofReceiptIsNotPromotion

missingSourceFirewall : Producer.ThinkPaysMissingSource → ⊥
missingSourceFirewall = Producer.thinkCannotPayMissingSource

humanReviewFirewall : Producer.ThinkPaysHumanReview → ⊥
humanReviewFirewall = Producer.thinkCannotPayHumanReview

zeroPriceFirewall : Access.ZeroPriceImpliesEffectiveAccess → ⊥
zeroPriceFirewall = Access.zeroPriceDoesNotImplyEffectiveAccess

machineRoleFirewall : Access.MachineClientImpliesCommercialRole → ⊥
machineRoleFirewall = Access.machineClientDoesNotImplyCommercialRole

settledContractFirewall : Access.SettledContractCreatesTruth → ⊥
settledContractFirewall = Access.settledContractDoesNotCreateTruth

byteAvailabilityProvenanceFirewall : History.ByteAvailabilityCreatesWriterProvenance → ⊥
byteAvailabilityProvenanceFirewall = History.byteAvailabilityIsNotWriterProvenance

projectionEvidenceFirewall : History.DeterministicProjectionCreatesSourceEvidence → ⊥
projectionEvidenceFirewall = History.deterministicProjectionIsNotSourceEvidence

materialisedHistoryFirewall : History.MaterialisedViewIsReplicatedHistory → ⊥
materialisedHistoryFirewall = History.materialisedViewIsNotReplicatedHistory

supersessionMutationFirewall : Supersession.SupersessionMutatesEarlierBytes → ⊥
supersessionMutationFirewall = Supersession.supersessionDoesNotMutateEarlierBytes

supersessionInvalidationFirewall : Supersession.SupersessionInvalidatesEarlierSource → ⊥
supersessionInvalidationFirewall = Supersession.supersessionDoesNotInvalidateEarlierSource

revisionFloatingFirewall : Supersession.ObservationCanFloatAcrossRevision → ⊥
revisionFloatingFirewall = Supersession.observationDoesNotFloatAcrossRevision

p2pAuthorityFirewall : Replication.PeerToPeerImpliesDecentralizedAuthority → ⊥
p2pAuthorityFirewall = Replication.peerToPeerDoesNotImplyDecentralizedAuthority

crdtEpistemicFirewall : Replication.CRDTConvergenceImpliesEpistemicAgreement → ⊥
crdtEpistemicFirewall = Replication.crdtConvergenceDoesNotImplyEpistemicAgreement

signedHeadMultiWriterFirewall : Replication.SignedHeadImpliesMultiWriterConvergence → ⊥
signedHeadMultiWriterFirewall = Replication.signedHeadDoesNotImplyMultiWriterConvergence

queryTruthFirewall : Replication.QueryDiscoveryImpliesClaimTruth → ⊥
queryTruthFirewall = Replication.queryDiscoveryDoesNotImplyClaimTruth
