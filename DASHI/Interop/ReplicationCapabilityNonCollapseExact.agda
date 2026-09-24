module DASHI.Interop.ReplicationCapabilityNonCollapseExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- REPLICATION CAPABILITY NON-COLLAPSE
--
-- Discussion-origin architecture: Johl Brown, 2026-09-17.
-- External technology roles were compared using BitTorrent, IPFS/IPLD/IPNS,
-- Hypercore/Autobase, OrbitDB, Peerbit, Automerge, Yjs, SQLite/RxDB,
-- PowerSync/Electric and Replicache as examples.  The capability axes and
-- non-collapse theorems below are DASHI synthesis; this is not a technology
-- ranking and does not assert deployment of any named project.
------------------------------------------------------------------------

data CapabilityAxis : Set where
  offlineFirst : CapabilityAxis
  localFirst : CapabilityAxis
  peerToPeer : CapabilityAxis
  decentralizedAuthority : CapabilityAxis
  cryptographicallyVerifiableProvenance : CapabilityAxis
  immutableBulkDistribution : CapabilityAxis
  immutableLinkedObjectGraph : CapabilityAxis
  authenticatedWriterHistory : CapabilityAxis
  deterministicMultiWriterProjection : CapabilityAxis
  semanticCRDTState : CapabilityAxis
  distributedDiscoveryQuery : CapabilityAxis
  localQueryMaterialisation : CapabilityAxis
  serverSelectiveSync : CapabilityAxis

data TechnologyFamily : Set where
  bittorrentFamily : TechnologyFamily
  ipfsIpldFamily : TechnologyFamily
  ipnsFamily : TechnologyFamily
  hypercoreAutobaseFamily : TechnologyFamily
  orbitDbFamily : TechnologyFamily
  peerbitFamily : TechnologyFamily
  automergeYjsFamily : TechnologyFamily
  sqliteRxdbPostgresFamily : TechnologyFamily
  powerSyncElectricFamily : TechnologyFamily
  replicacheFamily : TechnologyFamily

record CapabilityRole : Set where
  constructor capabilityRole
  field
    technologyFamily : TechnologyFamily
    primaryRole : CapabilityAxis
    roleDescription : String
    roleCreatesSemanticAuthority : Bool
    roleCreatesSemanticAuthorityIsFalse : roleCreatesSemanticAuthority ≡ false

open CapabilityRole public

bitTorrentRole : CapabilityRole
bitTorrentRole =
  capabilityRole bittorrentFamily immutableBulkDistribution
    "mature swarming of large immutable byte collections" false refl

ipfsRole : CapabilityRole
ipfsRole =
  capabilityRole ipfsIpldFamily immutableLinkedObjectGraph
    "content-addressed linked-object graph and retrieval" false refl

ipnsRole : CapabilityRole
ipnsRole =
  capabilityRole ipnsFamily authenticatedWriterHistory
    "signed mutable head to immutable snapshots; not generic multi-writer convergence"
    false refl

hypercoreAutobaseRole : CapabilityRole
hypercoreAutobaseRole =
  capabilityRole hypercoreAutobaseFamily deterministicMultiWriterProjection
    "signed append-only writer histories plus deterministic multi-writer materialized view"
    false refl

orbitDbRole : CapabilityRole
orbitDbRole =
  capabilityRole orbitDbFamily authenticatedWriterHistory
    "authenticated replicated operation history with database projections"
    false refl

peerbitRole : CapabilityRole
peerbitRole =
  capabilityRole peerbitFamily distributedDiscoveryQuery
    "P2P discovery/query/index/sharding capability precedent"
    false refl

automergeYjsRole : CapabilityRole
automergeYjsRole =
  capabilityRole automergeYjsFamily semanticCRDTState
    "semantically mergeable concurrent application/document state"
    false refl

localDatabaseRole : CapabilityRole
localDatabaseRole =
  capabilityRole sqliteRxdbPostgresFamily localQueryMaterialisation
    "consumer-local query/index/materialized operational state"
    false refl

selectiveSyncRole : CapabilityRole
selectiveSyncRole =
  capabilityRole powerSyncElectricFamily serverSelectiveSync
    "selective local synchronization against an authoritative backend"
    false refl

replicacheRole : CapabilityRole
replicacheRole =
  capabilityRole replicacheFamily offlineFirst
    "optimistic offline client mutation and server reconciliation precedent"
    false refl

------------------------------------------------------------------------
-- Capability axes remain orthogonal. Possession of one named capability does
-- not manufacture the others.
------------------------------------------------------------------------

data OfflineFirstImpliesLocalFirst : Set where
data LocalFirstImpliesPeerToPeer : Set where
data PeerToPeerImpliesDecentralizedAuthority : Set where
data PeerToPeerImpliesCryptographicProvenance : Set where
data CRDTConvergenceImpliesEpistemicAgreement : Set where
data SignedHeadImpliesMultiWriterConvergence : Set where
data QueryDiscoveryImpliesClaimTruth : Set where
data BulkAvailabilityImpliesApplicationWriterIdentity : Set where
data ServerSelectiveSyncImpliesDecentralizedAuthority : Set where

offlineFirstDoesNotImplyLocalFirst : OfflineFirstImpliesLocalFirst → ⊥
offlineFirstDoesNotImplyLocalFirst ()

localFirstDoesNotImplyPeerToPeer : LocalFirstImpliesPeerToPeer → ⊥
localFirstDoesNotImplyPeerToPeer ()

peerToPeerDoesNotImplyDecentralizedAuthority : PeerToPeerImpliesDecentralizedAuthority → ⊥
peerToPeerDoesNotImplyDecentralizedAuthority ()

peerToPeerDoesNotImplyCryptographicProvenance : PeerToPeerImpliesCryptographicProvenance → ⊥
peerToPeerDoesNotImplyCryptographicProvenance ()

crdtConvergenceDoesNotImplyEpistemicAgreement : CRDTConvergenceImpliesEpistemicAgreement → ⊥
crdtConvergenceDoesNotImplyEpistemicAgreement ()

signedHeadDoesNotImplyMultiWriterConvergence : SignedHeadImpliesMultiWriterConvergence → ⊥
signedHeadDoesNotImplyMultiWriterConvergence ()

queryDiscoveryDoesNotImplyClaimTruth : QueryDiscoveryImpliesClaimTruth → ⊥
queryDiscoveryDoesNotImplyClaimTruth ()

bulkAvailabilityDoesNotImplyApplicationWriterIdentity : BulkAvailabilityImpliesApplicationWriterIdentity → ⊥
bulkAvailabilityDoesNotImplyApplicationWriterIdentity ()

serverSelectiveSyncDoesNotImplyDecentralizedAuthority : ServerSelectiveSyncImpliesDecentralizedAuthority → ⊥
serverSelectiveSyncDoesNotImplyDecentralizedAuthority ()

canonicalCapabilityAxes : List CapabilityAxis
canonicalCapabilityAxes =
  offlineFirst ∷ localFirst ∷ peerToPeer ∷ decentralizedAuthority ∷
  cryptographicallyVerifiableProvenance ∷ immutableBulkDistribution ∷
  immutableLinkedObjectGraph ∷ authenticatedWriterHistory ∷
  deterministicMultiWriterProjection ∷ semanticCRDTState ∷
  distributedDiscoveryQuery ∷ localQueryMaterialisation ∷
  serverSelectiveSync ∷ []
