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
-- ERIC export executions cross the structured-search success bridge.
------------------------------------------------------------------------

ericQ1SuccessfulOutcome :
  SuccessfulObservedOutcome (Exec.outcome Exec.ericQ1ObservedExportExecution)
ericQ1SuccessfulOutcome =
  successful-observed-result
    642
    "ERIC live JSON result set (artifacts/digital-esd/eric/Q1/summary.json); pagination complete"
    "artifacts/digital-esd/eric/Q1/summary.json"
    "JSON"
    "HTTP 200; numFound=642; 4 pages fetched (642 docs); summarySha256=faa8cf35e1a34ec06a9cc97a816f78099752605aaf4a70c6b1493e1d24dd2e4b"

ericQ1SuccessfulExecution : SuccessfulExecutionForSurface Search.eric
ericQ1SuccessfulExecution =
  successful-execution-for-surface
    Exec.ericQ1ObservedExportExecution
    refl
    (Search.digitalEducationESD ∷ [])
    refl
    ericQ1SuccessfulOutcome

ericQ1StructuredSearchReceipt : Search.DatabaseExecutionReceipt Search.eric
ericQ1StructuredSearchReceipt = toStructuredSearchReceipt ericQ1SuccessfulExecution

ericQ2SuccessfulOutcome :
  SuccessfulObservedOutcome (Exec.outcome Exec.ericQ2ObservedExportExecution)
ericQ2SuccessfulOutcome =
  successful-observed-result
    290
    "ERIC live JSON result set (artifacts/digital-esd/eric/Q2/summary.json); pagination complete"
    "artifacts/digital-esd/eric/Q2/summary.json"
    "JSON"
    "HTTP 200; numFound=290; 2 pages fetched (290 docs); summarySha256=5a01ede4bcd53a8068f32fefd9e47d2e7f113a3acec214ed7b9609f47d0a110d"

ericQ2SuccessfulExecution : SuccessfulExecutionForSurface Search.eric
ericQ2SuccessfulExecution =
  successful-execution-for-surface
    Exec.ericQ2ObservedExportExecution
    refl
    (Search.digitalEducationESD ∷ [])
    refl
    ericQ2SuccessfulOutcome

ericQ2StructuredSearchReceipt : Search.DatabaseExecutionReceipt Search.eric
ericQ2StructuredSearchReceipt = toStructuredSearchReceipt ericQ2SuccessfulExecution

ericQ3SuccessfulOutcome :
  SuccessfulObservedOutcome (Exec.outcome Exec.ericQ3ObservedExportExecution)
ericQ3SuccessfulOutcome =
  successful-observed-result
    1594
    "ERIC live JSON result set (artifacts/digital-esd/eric/Q3/summary.json); pagination complete"
    "artifacts/digital-esd/eric/Q3/summary.json"
    "JSON"
    "HTTP 200; numFound=1594; 8 pages fetched (1594 docs); summarySha256=76ad0a9a971a6f9dadb90df29f18ce70533ab839ca78489ecf7f6b606e410c88"

ericQ3SuccessfulExecution : SuccessfulExecutionForSurface Search.eric
ericQ3SuccessfulExecution =
  successful-execution-for-surface
    Exec.ericQ3ObservedExportExecution
    refl
    (Search.reflexiveDigitalSustainability ∷ [])
    refl
    ericQ3SuccessfulOutcome

ericQ3StructuredSearchReceipt : Search.DatabaseExecutionReceipt Search.eric
ericQ3StructuredSearchReceipt = toStructuredSearchReceipt ericQ3SuccessfulExecution

ericQ4SuccessfulOutcome :
  SuccessfulObservedOutcome (Exec.outcome Exec.ericQ4ObservedExportExecution)
ericQ4SuccessfulOutcome =
  successful-observed-result
    41889
    "ERIC live JSON result set (artifacts/digital-esd/eric/Q4/summary.json); pagination complete"
    "artifacts/digital-esd/eric/Q4/summary.json"
    "JSON"
    "HTTP 200; numFound=41889; 210 pages fetched (41889 docs); summarySha256=bee52dd930f2ae6da0004ea56c0378f0445ad3ec0877a479f8fecb6ec557b53f"

ericQ4SuccessfulExecution : SuccessfulExecutionForSurface Search.eric
ericQ4SuccessfulExecution =
  successful-execution-for-surface
    Exec.ericQ4ObservedExportExecution
    refl
    (Search.lifecycleCircularity ∷ [])
    refl
    ericQ4SuccessfulOutcome

ericQ4StructuredSearchReceipt : Search.DatabaseExecutionReceipt Search.eric
ericQ4StructuredSearchReceipt = toStructuredSearchReceipt ericQ4SuccessfulExecution

ericQ5SuccessfulOutcome :
  SuccessfulObservedOutcome (Exec.outcome Exec.ericQ5ObservedExportExecution)
ericQ5SuccessfulOutcome =
  successful-observed-result
    214
    "ERIC live JSON result set (artifacts/digital-esd/eric/Q5/summary.json); pagination complete"
    "artifacts/digital-esd/eric/Q5/summary.json"
    "JSON"
    "HTTP 200; numFound=214; 2 pages fetched (214 docs); summarySha256=0302dfbc15b67be4d1664653bda4d5e0dcb99d547345f09c58588a2ea44feb90"

ericQ5SuccessfulExecution : SuccessfulExecutionForSurface Search.eric
ericQ5SuccessfulExecution =
  successful-execution-for-surface
    Exec.ericQ5ObservedExportExecution
    refl
    (Search.participantAgencyGovernance ∷ [])
    refl
    ericQ5SuccessfulOutcome

ericQ5StructuredSearchReceipt : Search.DatabaseExecutionReceipt Search.eric
ericQ5StructuredSearchReceipt = toStructuredSearchReceipt ericQ5SuccessfulExecution

ericQ6SuccessfulOutcome :
  SuccessfulObservedOutcome (Exec.outcome Exec.ericQ6ObservedExportExecution)
ericQ6SuccessfulOutcome =
  successful-observed-result
    293
    "ERIC live JSON result set (artifacts/digital-esd/eric/Q6/summary.json); pagination complete"
    "artifacts/digital-esd/eric/Q6/summary.json"
    "JSON"
    "HTTP 200; numFound=293; 2 pages fetched (293 docs); summarySha256=f96cf23bef0516d4f4fc2fa2d0cfb992cf187c67e7ca7389111b6eedb5122cb0"

ericQ6SuccessfulExecution : SuccessfulExecutionForSurface Search.eric
ericQ6SuccessfulExecution =
  successful-execution-for-surface
    Exec.ericQ6ObservedExportExecution
    refl
    (Search.longitudinalInstitutionalImpact ∷ [])
    refl
    ericQ6SuccessfulOutcome

ericQ6StructuredSearchReceipt : Search.DatabaseExecutionReceipt Search.eric
ericQ6StructuredSearchReceipt = toStructuredSearchReceipt ericQ6SuccessfulExecution

ericQ7SuccessfulOutcome :
  SuccessfulObservedOutcome (Exec.outcome Exec.ericQ7ObservedExportExecution)
ericQ7SuccessfulOutcome =
  successful-observed-result
    1675
    "ERIC live JSON result set (artifacts/digital-esd/eric/Q7/summary.json); pagination complete"
    "artifacts/digital-esd/eric/Q7/summary.json"
    "JSON"
    "HTTP 200; numFound=1675; 9 pages fetched (1675 docs); summarySha256=2cac198aa4c2270cdc30691edbf67387341026ea77adc671c9007ee1efe4a88d"

ericQ7SuccessfulExecution : SuccessfulExecutionForSurface Search.eric
ericQ7SuccessfulExecution =
  successful-execution-for-surface
    Exec.ericQ7ObservedExportExecution
    refl
    (Search.openInteroperabilityRepairability ∷ [])
    refl
    ericQ7SuccessfulOutcome

ericQ7StructuredSearchReceipt : Search.DatabaseExecutionReceipt Search.eric
ericQ7StructuredSearchReceipt = toStructuredSearchReceipt ericQ7SuccessfulExecution

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
  "The attempt ledger and the successful structured-search execution receipt remain distinct. A receipt crosses the bridge only with an explicit surface match, querySubmitted=true, an executedWithObservedResultSet outcome, and exportObserved. Existing Scopus/WoS access failures and ERIC transport failures cannot inhabit SuccessfulObservedOutcome; neither can the ERIC count-only executions because they retain exportNotObserved. The seven ERIC paginated export receipts (ericQ1-Q7ObservedExportExecution) successfully cross the bridge with retained JSON summaries and raw page sets. Conversion still creates only a successful database-execution receipt; deduplication, screening, extraction and corpus admission remain downstream payments."

