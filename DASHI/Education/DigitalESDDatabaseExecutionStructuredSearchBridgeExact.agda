module DASHI.Education.DigitalESDDatabaseExecutionStructuredSearchBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Education.DigitalESDDatabaseExecutionReceiptExact as Exec
import DASHI.Education.DigitalESDDatabaseTranslatedQueriesExact as Queries
import DASHI.Education.DigitalESDStructuredSearchExact as Search

------------------------------------------------------------------------
-- DATABASE EXECUTION -> STRUCTURED SEARCH SUCCESS BRIDGE
--
-- DigitalESDDatabaseExecutionReceiptExact records attempts, including failures
-- before submission. DigitalESDStructuredSearchExact intentionally accepts only
-- successful executions with retained counts/exports. This module is the thin
-- physical weld between those two receipt layers.
--
-- No failed attempt can cross the weld: the discriminator below has a
-- constructor only for an executedWithObservedResultSet carrying exportObserved.
------------------------------------------------------------------------

data SuccessfulObservedOutcome : Exec.ExecutionOutcome → Set where
  successful-observed-result :
    (resultCount : Nat) →
    (resultSetReference : String) →
    (exportReference : String) →
    (exportFormat : String) →
    (executionNote : String) →
    SuccessfulObservedOutcome
      (Exec.executedWithObservedResultSet
        resultCount
        resultSetReference
        (Exec.exportObserved exportReference exportFormat)
        executionNote)

record SuccessfulExecutionForSurface (surface : Search.SearchSurface) : Set where
  constructor successful-execution-for-surface
  field
    attempt : Exec.DatabaseExecutionReceipt
    attemptSurfaceMatches : Exec.surface attempt ≡ surface
    executedFamilies : List Search.SearchQueryFamily
    querySubmittedIsTrue : Exec.querySubmitted attempt ≡ true
    successfulOutcome : SuccessfulObservedOutcome (Exec.outcome attempt)

open SuccessfulExecutionForSurface public

toStructuredSearchReceipt :
  {surface : Search.SearchSurface} →
  SuccessfulExecutionForSurface surface →
  Search.DatabaseExecutionReceipt surface
toStructuredSearchReceipt
  (successful-execution-for-surface
    attempt
    surfaceMatches
    families
    submitted
    (successful-observed-result count resultSetRef exportRef exportFormat note)) =
  Search.database-execution-receipt
    families
    (Queries.exactTranslatedQuery (Exec.translatedQuery attempt))
    (Exec.attemptTimestamp attempt)
    exportRef
    count
    true refl
    true refl
    true refl
    true refl

------------------------------------------------------------------------
-- Existing blocked attempts are constructively unable to satisfy the bridge.
------------------------------------------------------------------------

scopusQ1BlockedAttemptCannotCreateSuccessfulOutcome :
  SuccessfulObservedOutcome (Exec.outcome Exec.scopusQ1Execution) → ⊥
scopusQ1BlockedAttemptCannotCreateSuccessfulOutcome ()

ericQ1TransportFailureCannotCreateSuccessfulOutcome :
  SuccessfulObservedOutcome (Exec.outcome Exec.ericQ1Execution) → ⊥
ericQ1TransportFailureCannotCreateSuccessfulOutcome ()

ericQ1ObservedCountWithoutExportCannotCreateSuccessfulOutcome :
  SuccessfulObservedOutcome (Exec.outcome Exec.ericQ1ObservedExecution) → ⊥
ericQ1ObservedCountWithoutExportCannotCreateSuccessfulOutcome ()

------------------------------------------------------------------------
-- Promotion firewalls.
------------------------------------------------------------------------

data AttemptCreatesSuccessfulStructuredReceipt : Set where
data SubmittedQueryCreatesObservedExport : Set where
data ObservedCountCreatesRetainedExport : Set where
data SuccessfulExecutionCreatesIncludedCorpus : Set where

attemptDoesNotCreateSuccessfulStructuredReceipt :
  AttemptCreatesSuccessfulStructuredReceipt → ⊥
attemptDoesNotCreateSuccessfulStructuredReceipt ()

submittedQueryDoesNotCreateObservedExport :
  SubmittedQueryCreatesObservedExport → ⊥
submittedQueryDoesNotCreateObservedExport ()

observedCountDoesNotCreateRetainedExport :
  ObservedCountCreatesRetainedExport → ⊥
observedCountDoesNotCreateRetainedExport ()

successfulExecutionDoesNotCreateIncludedCorpus :
  SuccessfulExecutionCreatesIncludedCorpus → ⊥
successfulExecutionDoesNotCreateIncludedCorpus ()

bridgeReading : String
bridgeReading =
  "The attempt ledger and the successful structured-search execution receipt remain distinct. A receipt crosses the bridge only with an explicit surface match, querySubmitted=true, an executedWithObservedResultSet outcome, and exportObserved. Existing Scopus/WoS access failures and ERIC transport failures cannot inhabit SuccessfulObservedOutcome; neither can the later ERIC count-only executions because they retain exportNotObserved. Conversion still creates only a successful database-execution receipt; deduplication, screening, extraction and corpus admission remain downstream payments."
