module DASHI.Wikimedia.IbrahimFirstLinkRepositoryHistoryCustodyPruningExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Wikimedia.IbrahimFirstLinkProducerOutputPathResidualExact as OutputPath

------------------------------------------------------------------------
-- IBRAHIM HISTORICAL FLN: PUBLIC REPOSITORY-HISTORY ROUTE PRUNING
--
-- Public Git history is useful negative archaeology here.  The relevant
-- producer and results README both enter the public repository in the initial
-- 2015-10-04 "ready" commit; no earlier committed revision of create_fln.py or
-- results/README.md exists from which to recover a path-consistent execution.
--
-- This does NOT prove that no historical uncommitted script, manual move,
-- cluster-side wrapper, or external custody artifact existed.  It only prunes
-- ordinary public committed history as a producer for that missing receipt.
------------------------------------------------------------------------

outputPathBoundary : OutputPath.ProducerOutputPathBoundary
outputPathBoundary = OutputPath.canonicalProducerOutputPathBoundary

producerRepositorySource : Attribution.AttributedSource
producerRepositorySource = Attribution.mkNoDOISource
  "Mark Ibrahim"
  "marksibrahim/wikipedia_network public Git history"
  "GitHub repository history; initial relevant commit 9dd11de2676860751b02c1bbb0aeee0afb7b2710"
  "2015-2019"
  "https://github.com/marksibrahim/wikipedia_network"
  (Attribution.namedSourceKind "public producer repository archaeology")
  "supports public committed-history chronology and path-content comparison only; does not prove exact historical execution, uncommitted cluster state, shard custody, or published-data identity"
  Attribution.publicAttribution

record RepositoryHistoryPruningReceipt : Set where
  constructor repository-history-pruning-receipt
  field
    createFlnFirstPublicCommitIsReady20151004 : Bool
    createFlnEarlierPublicCommittedRevisionRecovered : Bool
    resultsReadmeFirstPublicCommitIsReady20151004 : Bool
    resultsReadmeEarlierPublicCommittedRevisionRecovered : Bool
    currentCreateFlnStillUsesTrueFlnetwork : Bool
    committedMoveCopyRenameProducerRecovered : Bool
    incompleteResultsReadmeRetained : Bool
    vimSwapArtifactExistsInInitialTree : Bool
    vimSwapDecodedForHistoricalUrl : Bool
    publicGitHistoryCanPayMissingCustodyEdge : Bool
open RepositoryHistoryPruningReceipt public

canonicalRepositoryHistoryPruning : RepositoryHistoryPruningReceipt
canonicalRepositoryHistoryPruning = repository-history-pruning-receipt
  true false true false true false true true false false

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data NoCommittedReceiptMeansNoHistoricalReceipt : Set where
data VimSwapPresenceMeansRecoveredDataUrl : Set where
data InitialRepositorySnapshotMeansExecutedRevision : Set where
data LocalDesktopFlnMeansPublishedSameObject : Set where

noCommittedReceiptDoesNotProveNoHistoricalReceipt :
  NoCommittedReceiptMeansNoHistoricalReceipt → ⊥
noCommittedReceiptDoesNotProveNoHistoricalReceipt ()

swapPresenceDoesNotRecoverDataUrl : VimSwapPresenceMeansRecoveredDataUrl → ⊥
swapPresenceDoesNotRecoverDataUrl ()

initialSnapshotDoesNotProveExecutedRevision :
  InitialRepositorySnapshotMeansExecutedRevision → ⊥
initialSnapshotDoesNotProveExecutedRevision ()

localDesktopFilenameDoesNotPayPublishedSameObject :
  LocalDesktopFlnMeansPublishedSameObject → ⊥
localDesktopFilenameDoesNotPayPublishedSameObject ()

------------------------------------------------------------------------
-- Highest-alpha route after pruning.
------------------------------------------------------------------------

prunedRoute : String
prunedRoute =
  "Do not spend further proof-search budget looking for an older committed create_fln.py path fix: public path history has only the initial 2015-10-04 snapshot. Search instead for external execution/custody evidence: cluster job wrappers/logs, shell history or move/copy receipt, author-hosted published data/fln.json, archive mirrors, downloadable artifact metadata/hash, or another same-object receipt linking true_flnetwork shards to flnetwork inputs."

remainingPayment : String
remainingPayment =
  "Recover exact input dump object/hash and split receipt; recover an external execution/custody edge or historically executed path-consistent source object; acquire/hash the published fln.json; then compare parser-equivalent reproduction and semantic/object identity."

record RepositoryHistoryCustodyBoundary : Set where
  constructor repository-history-custody-boundary
  field
    publicCommittedHistoryInspected : Bool
    olderCommittedPathFixRoutePruned : Bool
    absenceOfCommittedReceiptPromotedToHistoricalAbsence : Bool
    uncommittedExternalCustodyRouteRemainsOpen : Bool
    publishedDataSameObjectStillUnpaid : Bool
    exactExecutedRevisionStillUnpaid : Bool
    exactDumpAndShardHashesStillUnpaid : Bool
open RepositoryHistoryCustodyBoundary public

canonicalRepositoryHistoryCustodyBoundary : RepositoryHistoryCustodyBoundary
canonicalRepositoryHistoryCustodyBoundary =
  repository-history-custody-boundary true true false true true true true
