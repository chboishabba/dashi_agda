module DASHI.Interop.DistributedEvidenceHistoryProjectionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Interop.SensibLawFederatedZOSAcquisitionExact as Federated
import DASHI.Interop.SensibLawWorldBucketPostgresMaterialisationExact as Postgres

------------------------------------------------------------------------
-- DISTRIBUTED EVIDENCE -> HISTORY -> PROJECTION BRAID
--
-- Discussion-origin architecture: Johl Brown, 2026-09-17.
-- External technology precedents discussed: BitTorrent, IPFS/IPLD/IPNS,
-- Hypercore/Autobase, OrbitDB/Peerbit, Automerge/Yjs, SQLite/RxDB,
-- PowerSync/Electric.  The typed carrier and non-collapse theorems below are
-- DASHI synthesis.  No named external technology is asserted deployed here.
--
-- Existing canonical DASHI/SensibLaw owners are reused for two boundaries:
--   * content-addressed/federated identity does not create semantic authority;
--   * Postgres is a durable local materialisation, not global semantic truth.
------------------------------------------------------------------------

data EvidenceLayer : Set where
  byteCollectionLayer : EvidenceLayer
  contentAddressedObjectLayer : EvidenceLayer
  signedObservationLayer : EvidenceLayer
  authenticatedHistoryLayer : EvidenceLayer
  deterministicProjectionLayer : EvidenceLayer
  queryIndexLayer : EvidenceLayer

record ImmutableSourceObject : Set where
  constructor immutableSourceObject
  field
    sourceIdentity : String
    exactByteDigest : String
    contentLocator : String
    bytesImmutableAtIdentity : Bool

open ImmutableSourceObject public

record SignedObservation : Set where
  constructor signedObservation
  field
    observedSource : ImmutableSourceObject
    producerIdentity : String
    signatureIdentity : String
    observationPayload : String
    observationCreatesSourceTruth : Bool
    observationCreatesSourceTruthIsFalse : observationCreatesSourceTruth ≡ false

open SignedObservation public

record AuthenticatedHistory : Set where
  constructor authenticatedHistory
  field
    historyIdentity : String
    retainedObservation : SignedObservation
    appendOnly : Bool
    writerAuthenticated : Bool
    historyCreatesSemanticAuthority : Bool
    historyCreatesSemanticAuthorityIsFalse : historyCreatesSemanticAuthority ≡ false

open AuthenticatedHistory public

record DeterministicProjection : Set where
  constructor deterministicProjection
  field
    projectionIdentity : String
    projectedHistory : AuthenticatedHistory
    consumerIdentity : String
    reducerIdentity : String
    deterministicReducer : Bool
    localMaterialisationIdentity : String
    projectionCreatesSourceEvidence : Bool
    projectionCreatesSourceEvidenceIsFalse : projectionCreatesSourceEvidence ≡ false

open DeterministicProjection public

record QueryIndex : Set where
  constructor queryIndex
  field
    indexedProjection : DeterministicProjection
    indexIdentity : String
    querySurface : String
    discoverabilityCreatesClaimTruth : Bool
    discoverabilityCreatesClaimTruthIsFalse : discoverabilityCreatesClaimTruth ≡ false

open QueryIndex public

record AuditableDerivedViewReceipt : Set where
  constructor auditableDerivedViewReceipt
  field
    exactSource : ImmutableSourceObject
    signedObservation : SignedObservation
    authenticatedHistory : AuthenticatedHistory
    deterministicProjection : DeterministicProjection
    queryIndex : QueryIndex
    sourceRetained : Bool
    sourceRetainedIsTrue : sourceRetained ≡ true
    observationRetained : Bool
    observationRetainedIsTrue : observationRetained ≡ true
    historyRetained : Bool
    historyRetainedIsTrue : historyRetained ≡ true
    projectionRetained : Bool
    projectionRetainedIsTrue : projectionRetained ≡ true
    promotesClaimTruth : Bool
    promotesClaimTruthIsFalse : promotesClaimTruth ≡ false

open AuditableDerivedViewReceipt public

mkAuditableDerivedViewReceipt :
  (source : ImmutableSourceObject) →
  (observation : SignedObservation) →
  (history : AuthenticatedHistory) →
  (projection : DeterministicProjection) →
  (index : QueryIndex) →
  AuditableDerivedViewReceipt
mkAuditableDerivedViewReceipt source observation history projection index =
  auditableDerivedViewReceipt
    source observation history projection index
    true refl true refl true refl true refl false refl

------------------------------------------------------------------------
-- Canonical synthetic fixture. This demonstrates the architecture only.
------------------------------------------------------------------------

exampleSource : ImmutableSourceObject
exampleSource =
  immutableSourceObject
    "source:example"
    "sha256:example"
    "cid-or-torrent:example"
    true

exampleObservation : SignedObservation
exampleObservation =
  signedObservation
    exampleSource
    "producer:example"
    "signature:example"
    "observed proposition payload"
    false refl

exampleHistory : AuthenticatedHistory
exampleHistory =
  authenticatedHistory
    "history:example"
    exampleObservation
    true true
    false refl

exampleProjection : DeterministicProjection
exampleProjection =
  deterministicProjection
    "projection:example"
    exampleHistory
    "consumer:example"
    "reducer:example"
    true
    "postgres/local-view:example"
    false refl

exampleIndex : QueryIndex
exampleIndex =
  queryIndex
    exampleProjection
    "index:example"
    "query/search/index"
    false refl

exampleAuditableDerivedView : AuditableDerivedViewReceipt
exampleAuditableDerivedView =
  mkAuditableDerivedViewReceipt
    exampleSource exampleObservation exampleHistory exampleProjection exampleIndex

------------------------------------------------------------------------
-- Existing canonical boundary reuse.
------------------------------------------------------------------------

federatedContentBoundary : Federated.FederatedContentBoundary
federatedContentBoundary = Federated.canonicalFederatedContentBoundary

postgresMaterialisationBoundary : Postgres.PostgresWorldBucketBoundary
postgresMaterialisationBoundary = Postgres.canonicalPostgresWorldBucketBoundary

------------------------------------------------------------------------
-- Non-collapse firewalls.
------------------------------------------------------------------------

data ByteAvailabilityCreatesWriterProvenance : Set where
data CIDEqualityCreatesObservationEquality : Set where
data SignedHistoryCreatesMaterialisedAuthority : Set where
data DeterministicProjectionCreatesSourceEvidence : Set where
data QueryDiscoverabilityCreatesClaimTruth : Set where
data DerivedViewReconstructsExactSource : Set where
data MaterialisedViewIsReplicatedHistory : Set where

data SameDigestCreatesSameSemanticClaim : Set where

byteAvailabilityIsNotWriterProvenance : ByteAvailabilityCreatesWriterProvenance → ⊥
byteAvailabilityIsNotWriterProvenance ()

cidEqualityIsNotObservationEquality : CIDEqualityCreatesObservationEquality → ⊥
cidEqualityIsNotObservationEquality ()

signedHistoryIsNotMaterialisedAuthority : SignedHistoryCreatesMaterialisedAuthority → ⊥
signedHistoryIsNotMaterialisedAuthority ()

deterministicProjectionIsNotSourceEvidence : DeterministicProjectionCreatesSourceEvidence → ⊥
deterministicProjectionIsNotSourceEvidence ()

queryDiscoverabilityIsNotClaimTruth : QueryDiscoverabilityCreatesClaimTruth → ⊥
queryDiscoverabilityIsNotClaimTruth ()

derivedViewDoesNotReconstructExactSource : DerivedViewReconstructsExactSource → ⊥
derivedViewDoesNotReconstructExactSource ()

materialisedViewIsNotReplicatedHistory : MaterialisedViewIsReplicatedHistory → ⊥
materialisedViewIsNotReplicatedHistory ()

sameDigestDoesNotCreateSameSemanticClaim : SameDigestCreatesSameSemanticClaim → ⊥
sameDigestDoesNotCreateSameSemanticClaim ()

canonicalLayerPath : List EvidenceLayer
canonicalLayerPath =
  byteCollectionLayer ∷ contentAddressedObjectLayer ∷ signedObservationLayer ∷
  authenticatedHistoryLayer ∷ deterministicProjectionLayer ∷ queryIndexLayer ∷ []
