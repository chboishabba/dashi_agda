module DASHI.Education.DigitalESDDatabaseExecutionReceiptExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Education.DigitalESDDatabaseTranslatedQueriesExact as Queries
import DASHI.Education.DigitalESDStructuredSearchExact as Search

------------------------------------------------------------------------
-- EXACT DATABASE EXECUTION / RESULT-SET RECEIPTS
--
-- A translated query is not an execution. An execution attempt may itself stop
-- before submission. Blocked-before-submission states therefore carry neither
-- result counts nor exports by construction.
------------------------------------------------------------------------

data ExportState : Set where
  exportObserved : String → String → ExportState
  exportNotObserved : String → ExportState

data ExecutionOutcome : Set where
  executedWithObservedResultSet :
    Nat → String → ExportState → String → ExecutionOutcome
  accessBlockedBeforeSubmission : String → ExecutionOutcome
  authenticationBlockedBeforeSubmission : String → ExecutionOutcome
  interfaceFailureBeforeSubmission : String → ExecutionOutcome

record DatabaseExecutionReceipt : Set where
  constructor database-execution-receipt
  field
    translatedQuery : Queries.TranslatedQueryReceipt
    surface : Search.SearchSurface
    executionAttempted : Bool
    executionAttemptedIsTrue : executionAttempted ≡ true
    querySubmitted : Bool
    querySubmittedIsFalse : querySubmitted ≡ false
    attemptTimestamp : String
    platformEntrypoint : String
    outcome : ExecutionOutcome
    executionEnvironment : String
    promotionBoundary : String

open DatabaseExecutionReceipt public

------------------------------------------------------------------------
-- 2026-09-16 execution attempts from the current ChatGPT web execution
-- environment. Both database search entrypoints returned HTTP 403 before the
-- query text could be submitted. Therefore all fourteen translated queries
-- receive query-specific attempt receipts but no result count/export payload.
------------------------------------------------------------------------

attemptTimestamp20260916 : String
attemptTimestamp20260916 = "2026-09-16T19:43:00+10:00"

scopusEntrypoint : String
scopusEntrypoint = "https://www.scopus.com/search/form.uri?display=advanced"

wosCoreEntrypoint : String
wosCoreEntrypoint = "https://www.webofscience.com/wos/woscc/basic-search"

scopusBlockedOutcome : ExecutionOutcome
scopusBlockedOutcome =
  accessBlockedBeforeSubmission
    "HTTP 403 at Scopus Advanced Search entrypoint in this execution environment"

wosBlockedOutcome : ExecutionOutcome
wosBlockedOutcome =
  accessBlockedBeforeSubmission
    "HTTP 403 at Web of Science Core Collection entrypoint in this execution environment"

scopusBlockedExecution : Queries.TranslatedQueryReceipt → DatabaseExecutionReceipt
scopusBlockedExecution q = database-execution-receipt
  q
  Search.scopus
  true refl
  false refl
  attemptTimestamp20260916
  scopusEntrypoint
  scopusBlockedOutcome
  "ChatGPT web retrieval environment; platform returned HTTP 403 before query submission"
  "attempt receipt only: no query submission, result count, export, deduplication, screening, eligibility or evidence payment is created"

wosBlockedExecution : Queries.TranslatedQueryReceipt → DatabaseExecutionReceipt
wosBlockedExecution q = database-execution-receipt
  q
  Search.webOfScience
  true refl
  false refl
  attemptTimestamp20260916
  wosCoreEntrypoint
  wosBlockedOutcome
  "ChatGPT web retrieval environment; platform returned HTTP 403 before query submission"
  "attempt receipt only: no query submission, result count, export, deduplication, screening, eligibility or evidence payment is created"

scopusQ1Execution : DatabaseExecutionReceipt
scopusQ1Execution = scopusBlockedExecution Queries.scopusQ1DigitalEducationESD

scopusQ2Execution : DatabaseExecutionReceipt
scopusQ2Execution = scopusBlockedExecution Queries.scopusQ2Transformation

scopusQ3Execution : DatabaseExecutionReceipt
scopusQ3Execution = scopusBlockedExecution Queries.scopusQ3ReflexiveSustainability

scopusQ4Execution : DatabaseExecutionReceipt
scopusQ4Execution = scopusBlockedExecution Queries.scopusQ4LifecycleCircularity

scopusQ5Execution : DatabaseExecutionReceipt
scopusQ5Execution = scopusBlockedExecution Queries.scopusQ5ParticipantGovernance

scopusQ6Execution : DatabaseExecutionReceipt
scopusQ6Execution = scopusBlockedExecution Queries.scopusQ6LongitudinalInstitutional

scopusQ7Execution : DatabaseExecutionReceipt
scopusQ7Execution = scopusBlockedExecution Queries.scopusQ7OpenInteroperableRepairable

wosQ1Execution : DatabaseExecutionReceipt
wosQ1Execution = wosBlockedExecution Queries.wosQ1DigitalEducationESD

wosQ2Execution : DatabaseExecutionReceipt
wosQ2Execution = wosBlockedExecution Queries.wosQ2Transformation

wosQ3Execution : DatabaseExecutionReceipt
wosQ3Execution = wosBlockedExecution Queries.wosQ3ReflexiveSustainability

wosQ4Execution : DatabaseExecutionReceipt
wosQ4Execution = wosBlockedExecution Queries.wosQ4LifecycleCircularity

wosQ5Execution : DatabaseExecutionReceipt
wosQ5Execution = wosBlockedExecution Queries.wosQ5ParticipantGovernance

wosQ6Execution : DatabaseExecutionReceipt
wosQ6Execution = wosBlockedExecution Queries.wosQ6LongitudinalInstitutional

wosQ7Execution : DatabaseExecutionReceipt
wosQ7Execution = wosBlockedExecution Queries.wosQ7OpenInteroperableRepairable

canonicalExecutionReceipts : List DatabaseExecutionReceipt
canonicalExecutionReceipts =
  scopusQ1Execution
  ∷ scopusQ2Execution
  ∷ scopusQ3Execution
  ∷ scopusQ4Execution
  ∷ scopusQ5Execution
  ∷ scopusQ6Execution
  ∷ scopusQ7Execution
  ∷ wosQ1Execution
  ∷ wosQ2Execution
  ∷ wosQ3Execution
  ∷ wosQ4Execution
  ∷ wosQ5Execution
  ∷ wosQ6Execution
  ∷ wosQ7Execution
  ∷ []

executionReceiptCount : Nat
executionReceiptCount = 14

------------------------------------------------------------------------
-- Promotion firewalls.
------------------------------------------------------------------------

data BlockedExecutionCreatesObservedResultCount : Set where
data BlockedExecutionCreatesExport : Set where
data ExecutionReceiptCreatesIncludedCorpus : Set where
data ExecutionAttemptEqualsQuerySubmission : Set where
data ResultCountEqualsSearchCompleteness : Set where

blockedExecutionDoesNotCreateObservedResultCount :
  BlockedExecutionCreatesObservedResultCount → ⊥
blockedExecutionDoesNotCreateObservedResultCount ()

blockedExecutionDoesNotCreateExport : BlockedExecutionCreatesExport → ⊥
blockedExecutionDoesNotCreateExport ()

executionReceiptDoesNotCreateIncludedCorpus :
  ExecutionReceiptCreatesIncludedCorpus → ⊥
executionReceiptDoesNotCreateIncludedCorpus ()

executionAttemptDoesNotEqualQuerySubmission :
  ExecutionAttemptEqualsQuerySubmission → ⊥
executionAttemptDoesNotEqualQuerySubmission ()

resultCountDoesNotEqualSearchCompleteness : ResultCountEqualsSearchCompleteness → ⊥
resultCountDoesNotEqualSearchCompleteness ()

record DatabaseExecutionBoundary : Set where
  constructor database-execution-boundary
  field
    exactTranslatedQueryRetained : Bool
    exactTranslatedQueryRetainedIsTrue : exactTranslatedQueryRetained ≡ true
    attemptTimestampRetained : Bool
    attemptTimestampRetainedIsTrue : attemptTimestampRetained ≡ true
    platformEntrypointRetained : Bool
    platformEntrypointRetainedIsTrue : platformEntrypointRetained ≡ true
    blockedBeforeSubmissionDistinctFromZeroResults : Bool
    blockedBeforeSubmissionDistinctFromZeroResultsIsTrue :
      blockedBeforeSubmissionDistinctFromZeroResults ≡ true
    blockedExecutionCarriesNoResultCountOrExport : Bool
    blockedExecutionCarriesNoResultCountOrExportIsTrue :
      blockedExecutionCarriesNoResultCountOrExport ≡ true
    executionAttemptCreatesIncludedCorpus : Bool
    executionAttemptCreatesIncludedCorpusIsFalse :
      executionAttemptCreatesIncludedCorpus ≡ false

open DatabaseExecutionBoundary public

canonicalDatabaseExecutionBoundary : DatabaseExecutionBoundary
canonicalDatabaseExecutionBoundary = database-execution-boundary
  true refl
  true refl
  true refl
  true refl
  true refl
  false refl

executionReceiptReading : String
executionReceiptReading =
  "All fourteen frozen Scopus/Web-of-Science translations received explicit execution-attempt receipts on 2026-09-16. Both live database entrypoints returned HTTP 403 before query submission in the available web execution environment. The blocked outcome constructors cannot carry result counts or exports, so access failure cannot be mistaken for zero results. A future authenticated/institutional execution must create new executedWithObservedResultSet receipts retaining the exact translated query, count, result-set identity/export state and execution evidence."
