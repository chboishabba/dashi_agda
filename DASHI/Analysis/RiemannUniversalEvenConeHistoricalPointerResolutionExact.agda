module DASHI.Analysis.RiemannUniversalEvenConeHistoricalPointerResolutionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Analysis.RiemannUniversalEvenConeHistoricalSourceArchaeologyExact as Archaeology

------------------------------------------------------------------------
-- HISTORICAL POINTER RESOLUTION STATUS
--
-- The archaeology owner preserves two kinds of historical locator:
--
--   * transient Git branch/commit/path coordinates;
--   * durable content-addressed archive identity (archive name + CID/IPFS +
--     recorded witness hash).
--
-- A fresh 2026-09-16 connector check could no longer resolve the recorded
-- historical branch/commit through the connected repository surface.  The
-- content-addressed tuple remains preserved in the Agda receipt.  This owner
-- therefore prevents the stale Git locator from being interpreted as current
-- source custody while retaining the archive pointer as the preferred recovery
-- key.
--
-- Non-resolution is not deletion/nonexistence evidence and does not identify a
-- substitute taper.
------------------------------------------------------------------------

archivePointer : Archaeology.HistoricalAristotleArchivePointer
archivePointer = Archaeology.currentHistoricalAristotleArchivePointer

record HistoricalPointerResolutionBoundary : Set where
  constructor historical-pointer-resolution-boundary
  field
    contentAddressedArchivePointerRecorded : Bool
    archiveNameRecorded : Bool
    cidOrIpfsIdentityRecorded : Bool
    witnessHashRecorded : Bool

    historicalBranchCurrentlyResolvable : Bool
    historicalCommitCurrentlyResolvable : Bool
    retainedAggregateCurrentlyFetchableViaRecordedGitLocator : Bool

    archiveBytesAcquired : Bool
    archiveWitnessVerified : Bool
    archiveContentsSearched : Bool
    exactHistoricalTaperSourceRecovered : Bool

    staleGitLocatorInvalidatesArchivePointer : Bool
    unresolvedGitLocatorProvesHistoricalSourceDeleted : Bool
    pointerAloneCreatesLeanCustody : Bool
    pointerAloneCreatesKernelReceipt : Bool

    preferredRecoveryKey : String
    nextResidual : String
open HistoricalPointerResolutionBoundary public

canonicalHistoricalPointerResolutionBoundary : HistoricalPointerResolutionBoundary
canonicalHistoricalPointerResolutionBoundary =
  historical-pointer-resolution-boundary
    true
    true
    true
    true
    false
    false
    false
    false
    false
    false
    false
    false
    false
    false
    false
    "archive name + CID/IPFS identity + recorded witness hash"
    "recover the original Aristotle archive using the preserved content-addressed tuple; verify the retrieved bytes against the recorded witness before searching for literalWeilSameOrdinateEvenCone, primeEvenConeUnreachable, and the exact taper definition. Do not infer deletion from the stale Git locator and do not substitute another taper."

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data StaleGitLocatorDestroysContentAddressedIdentity : Set where
data PointerCreatesLeanProofCustody : Set where

data PointerCreatesKernelCertification : Set where

staleGitLocatorDoesNotDestroyContentAddressedIdentity :
  StaleGitLocatorDestroysContentAddressedIdentity -> ⊥
staleGitLocatorDoesNotDestroyContentAddressedIdentity ()

pointerDoesNotCreateLeanProofCustody : PointerCreatesLeanProofCustody -> ⊥
pointerDoesNotCreateLeanProofCustody ()

pointerDoesNotCreateKernelCertification : PointerCreatesKernelCertification -> ⊥
pointerDoesNotCreateKernelCertification ()
