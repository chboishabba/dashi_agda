module DASHI.Law.SensibLawOfflinePabaiLoopRustReceiptV01Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- EXACT RUST OFFLINE PABAI LOOP RECEIPT v0.1
--
-- Source artefact:
--   offline-pabai-loop-v01.json
-- Rust PR #9 exact head:
--   390b058a00c5d20e6ce947f526f190b56747e69b
--
-- This owner imports only the bounded runtime receipt. It does not upgrade the
-- Rust scheduler/loop to semantic authority, legal holding authority, world
-- truth, admission authority, or publication authority.
------------------------------------------------------------------------

rustRepository : String
rustRepository = "chboishabba/slr"

rustPullRequest : Nat
rustPullRequest = 9

rustExactHead : String
rustExactHead = "390b058a00c5d20e6ce947f526f190b56747e69b"

receiptSchemaVersion : String
receiptSchemaVersion = "sensiblaw.offline-proof-search-loop-receipt.v0_1"

receiptAuthority : String
receiptAuthority = "experimental_candidate_only"

receiptNetworkRequests : Nat
receiptNetworkRequests = 0

consumerRef : String
consumerRef = "consumer:pabai-duty-route"

residualRef : String
residualRef = "residual:positive-operational-act-comparator"

missingPropositionRef : String
missingPropositionRef = "prop:cullen-positive-operational-act"

selectedMoveRef : String
selectedMoveRef = "move:persisted-cullen-comparator"

selectedSourceRevisionRef : String
selectedSourceRevisionRef = "source:cullen:rev:1"

selectedStrategy : String
selectedStrategy = "PersistedAuthorityReceipt"

artifactRef : String
artifactRef = "fixture:cullen"

artifactDocumentRef : String
artifactDocumentRef = "doc:cullen"

artifactSourceRevisionRef : String
artifactSourceRevisionRef = "source:cullen:rev:1"

artifactBytesDigestRef : String
artifactBytesDigestRef = "sha256:cullen"

artifactNetworkRequests : Nat
artifactNetworkRequests = 0

bridgeDocumentRef : String
bridgeDocumentRef = "doc:cullen"

bridgeCanonicalTextSHA256 : String
bridgeCanonicalTextSHA256 = "sha256:cullen"

bridgeGraphRef : String
bridgeGraphRef = "graph:cullen"

correspondenceDocumentRef : String
correspondenceDocumentRef = "doc:cullen"

correspondenceGraphRef : String
correspondenceGraphRef = "graph:cullen"

correspondencePropositionRef : String
correspondencePropositionRef = "prop:cullen-positive-operational-act"

correspondenceWorldTruthClaimed : Bool
correspondenceWorldTruthClaimed = false

correspondenceLegalHoldingClaimed : Bool
correspondenceLegalHoldingClaimed = false

assessmentGrade : String
assessmentGrade = "ComparatorOnly"

correspondenceStatus : String
correspondenceStatus = "ReviewedSupported"

observedProofReduction : Nat
observedProofReduction = 2

frontierDisposition : String
frontierDisposition = "Narrowed"

changedCoordinate : String
changedCoordinate = "prop:cullen-positive-operational-act"

wakeRequestCount : Nat
wakeRequestCount = 0

nextMoveRef : String
nextMoveRef = "move:persisted-next-authority"

nextMoveStrategy : String
nextMoveStrategy = "PersistedAuthorityReceipt"

deltaAuthority : String
deltaAuthority = "experimental_candidate_only"

iterationAuthority : String
iterationAuthority = "experimental_candidate_only"

------------------------------------------------------------------------
-- Exact receipt welds.
------------------------------------------------------------------------

selectedSourceMatchesArtifactSource :
  selectedSourceRevisionRef ≡ artifactSourceRevisionRef
selectedSourceMatchesArtifactSource = refl

artifactDocumentMatchesBridgeDocument :
  artifactDocumentRef ≡ bridgeDocumentRef
artifactDocumentMatchesBridgeDocument = refl

artifactDigestMatchesBridgeDigest :
  artifactBytesDigestRef ≡ bridgeCanonicalTextSHA256
artifactDigestMatchesBridgeDigest = refl

bridgeDocumentMatchesCorrespondenceDocument :
  bridgeDocumentRef ≡ correspondenceDocumentRef
bridgeDocumentMatchesCorrespondenceDocument = refl

bridgeGraphMatchesCorrespondenceGraph :
  bridgeGraphRef ≡ correspondenceGraphRef
bridgeGraphMatchesCorrespondenceGraph = refl

missingPropositionMatchesCorrespondence :
  missingPropositionRef ≡ correspondencePropositionRef
missingPropositionMatchesCorrespondence = refl

changedCoordinateMatchesCorrespondence :
  changedCoordinate ≡ correspondencePropositionRef
changedCoordinateMatchesCorrespondence = refl

receiptIsNetworkFree : receiptNetworkRequests ≡ 0
receiptIsNetworkFree = refl

artifactIsNetworkFree : artifactNetworkRequests ≡ 0
artifactIsNetworkFree = refl

worldTruthRemainsUnclaimed : correspondenceWorldTruthClaimed ≡ false
worldTruthRemainsUnclaimed = refl

legalHoldingRemainsUnclaimed : correspondenceLegalHoldingClaimed ≡ false
legalHoldingRemainsUnclaimed = refl

------------------------------------------------------------------------
-- Typed bounded receipt.
------------------------------------------------------------------------

record OfflinePabaiLoopReceiptV01 : Set where
  constructor offlinePabaiLoopReceiptV01
  field
    schemaVersion : String
    authority : String
    networkRequests : Nat
    proofGapConsumer : String
    proofGapResidual : String
    proofGapMissingProposition : String
    firstMove : String
    firstSourceRevision : String
    firstStrategy : String
    localArtifact : String
    localDocument : String
    localDigest : String
    bridgeGraph : String
    proposition : String
    worldTruthClaimed : Bool
    legalHoldingClaimed : Bool
    grade : String
    reviewedStatus : String
    proofReduction : Nat
    disposition : String
    changedCoordinateRef : String
    wakeCount : Nat
    nextMove : String
    nextStrategy : String
    deltaAuthorityRef : String
    iterationAuthorityRef : String

open OfflinePabaiLoopReceiptV01 public

canonicalOfflinePabaiLoopReceiptV01 : OfflinePabaiLoopReceiptV01
canonicalOfflinePabaiLoopReceiptV01 = offlinePabaiLoopReceiptV01
  receiptSchemaVersion
  receiptAuthority
  receiptNetworkRequests
  consumerRef
  residualRef
  missingPropositionRef
  selectedMoveRef
  selectedSourceRevisionRef
  selectedStrategy
  artifactRef
  artifactDocumentRef
  artifactBytesDigestRef
  bridgeGraphRef
  correspondencePropositionRef
  correspondenceWorldTruthClaimed
  correspondenceLegalHoldingClaimed
  assessmentGrade
  correspondenceStatus
  observedProofReduction
  frontierDisposition
  changedCoordinate
  wakeRequestCount
  nextMoveRef
  nextMoveStrategy
  deltaAuthority
  iterationAuthority

------------------------------------------------------------------------
-- No-collapse firewalls.
------------------------------------------------------------------------

data ExperimentalReceiptEqualsSemanticAuthority : Set where
data ComparatorReceiptEqualsLegalHolding : Set where
data NarrowedFrontierEqualsProofClosure : Set where
data ZeroNetworkRequestsMeansNoLocalComputationCost : Set where
data ReviewedCorrespondenceEqualsWorldTruth : Set where
data EmptyWakeSetMeansNoFutureConsumerCanEverWake : Set where

experimentalReceiptDoesNotEqualSemanticAuthority :
  ExperimentalReceiptEqualsSemanticAuthority → ⊥
experimentalReceiptDoesNotEqualSemanticAuthority ()

comparatorReceiptDoesNotEqualLegalHolding :
  ComparatorReceiptEqualsLegalHolding → ⊥
comparatorReceiptDoesNotEqualLegalHolding ()

narrowedDoesNotEqualClosed : NarrowedFrontierEqualsProofClosure → ⊥
narrowedDoesNotEqualClosed ()

zeroNetworkDoesNotEraseLocalCost :
  ZeroNetworkRequestsMeansNoLocalComputationCost → ⊥
zeroNetworkDoesNotEraseLocalCost ()

reviewedCorrespondenceDoesNotEqualTruth :
  ReviewedCorrespondenceEqualsWorldTruth → ⊥
reviewedCorrespondenceDoesNotEqualTruth ()

emptyWakeSetDoesNotForbidFutureWake :
  EmptyWakeSetMeansNoFutureConsumerCanEverWake → ⊥
emptyWakeSetDoesNotForbidFutureWake ()

record OfflinePabaiRustReceiptBoundary : Set where
  constructor offlinePabaiRustReceiptBoundary
  field
    exactRustHeadPinned : Bool
    exactRustHeadPinnedIsTrue : exactRustHeadPinned ≡ true
    networkFreeExecutionPinned : Bool
    networkFreeExecutionPinnedIsTrue : networkFreeExecutionPinned ≡ true
    sourceDocumentDigestPropositionWeldsPinned : Bool
    sourceDocumentDigestPropositionWeldsPinnedIsTrue :
      sourceDocumentDigestPropositionWeldsPinned ≡ true
    candidateOnlyAuthorityRetained : Bool
    candidateOnlyAuthorityRetainedIsTrue : candidateOnlyAuthorityRetained ≡ true
    narrowedFrontierClaimedClosed : Bool
    narrowedFrontierClaimedClosedIsFalse : narrowedFrontierClaimedClosed ≡ false
    worldTruthClaimedByReceipt : Bool
    worldTruthClaimedByReceiptIsFalse : worldTruthClaimedByReceipt ≡ false
    legalHoldingClaimedByReceipt : Bool
    legalHoldingClaimedByReceiptIsFalse : legalHoldingClaimedByReceipt ≡ false

canonicalOfflinePabaiRustReceiptBoundary : OfflinePabaiRustReceiptBoundary
canonicalOfflinePabaiRustReceiptBoundary = offlinePabaiRustReceiptBoundary
  true refl true refl true refl true refl false refl false refl false refl
