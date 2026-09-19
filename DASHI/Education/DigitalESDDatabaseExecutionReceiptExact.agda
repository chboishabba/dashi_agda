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
-- result counts nor exports by construction. querySubmitted remains an ordinary
-- receipt coordinate so future successful executions may set it to true.
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
  false
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
  false
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


------------------------------------------------------------------------
-- 2026-09-19 ERIC public-API execution attempt.
--
-- The exact ERIC translations and public API syntax are now frozen, but this
-- execution environment's web transport refused direct access to
-- api.ies.ed.gov before a response body/result count could be observed.
-- Therefore these are interface-failure-before-submission receipts only.
------------------------------------------------------------------------

attemptTimestamp20260919 : String
attemptTimestamp20260919 = "2026-09-19T13:31:00+10:00"

ericAPIEntrypoint : String
ericAPIEntrypoint = "https://api.ies.ed.gov/eric/"

ericInterfaceFailureOutcome : ExecutionOutcome
ericInterfaceFailureOutcome =
  interfaceFailureBeforeSubmission
    "current web transport refused direct api.ies.ed.gov access before a result response could be observed"

ericInterfaceFailureExecution : Queries.TranslatedQueryReceipt → DatabaseExecutionReceipt
ericInterfaceFailureExecution q = database-execution-receipt
  q
  Search.eric
  true refl
  false
  attemptTimestamp20260919
  ericAPIEntrypoint
  ericInterfaceFailureOutcome
  "ChatGPT web retrieval environment; official ERIC API syntax verified, direct API response retrieval unavailable in this transport"
  "attempt receipt only: no observed API response, result count, export, deduplication, screening, eligibility or evidence payment is created"

ericQ1Execution : DatabaseExecutionReceipt
ericQ1Execution = ericInterfaceFailureExecution Queries.ericQ1DigitalEducationESD

ericQ2Execution : DatabaseExecutionReceipt
ericQ2Execution = ericInterfaceFailureExecution Queries.ericQ2Transformation

ericQ3Execution : DatabaseExecutionReceipt
ericQ3Execution = ericInterfaceFailureExecution Queries.ericQ3ReflexiveSustainability

ericQ4Execution : DatabaseExecutionReceipt
ericQ4Execution = ericInterfaceFailureExecution Queries.ericQ4LifecycleCircularity

ericQ5Execution : DatabaseExecutionReceipt
ericQ5Execution = ericInterfaceFailureExecution Queries.ericQ5ParticipantGovernance

ericQ6Execution : DatabaseExecutionReceipt
ericQ6Execution = ericInterfaceFailureExecution Queries.ericQ6LongitudinalInstitutional

ericQ7Execution : DatabaseExecutionReceipt
ericQ7Execution = ericInterfaceFailureExecution Queries.ericQ7OpenInteroperableRepairable


------------------------------------------------------------------------
-- 2026-09-19 IEEE Xplore and ACM DL search-result retrieval attempts.
--
-- Exact query translations exist, but the current web transport could not
-- retrieve the live search-result pages. These remain interface failures with
-- no observed counts/exports and therefore cannot cross the success bridge.
------------------------------------------------------------------------

ieeeEntrypoint : String
ieeeEntrypoint = "https://ieeexplore.ieee.org/search/searchresult.jsp"

acmEntrypoint : String
acmEntrypoint = "https://dl.acm.org/action/doSearch"

ieeeInterfaceFailureOutcome : ExecutionOutcome
ieeeInterfaceFailureOutcome =
  interfaceFailureBeforeSubmission
    "current web transport could not retrieve an IEEE Xplore search-result page for the submitted URL"

acmInterfaceFailureOutcome : ExecutionOutcome
acmInterfaceFailureOutcome =
  interfaceFailureBeforeSubmission
    "current web transport could not retrieve an ACM Digital Library search-result page for the submitted URL"

ieeeInterfaceFailureExecution : Queries.TranslatedQueryReceipt → DatabaseExecutionReceipt
ieeeInterfaceFailureExecution q = database-execution-receipt
  q
  Search.ieeeXplore
  true refl
  false
  attemptTimestamp20260919
  ieeeEntrypoint
  ieeeInterfaceFailureOutcome
  "ChatGPT web retrieval environment; exact IEEE translation available, live search-result retrieval inaccessible"
  "attempt receipt only: no observed result page, count, export, deduplication, screening, eligibility or evidence payment is created"

acmInterfaceFailureExecution : Queries.TranslatedQueryReceipt → DatabaseExecutionReceipt
acmInterfaceFailureExecution q = database-execution-receipt
  q
  Search.acmDigitalLibrary
  true refl
  false
  attemptTimestamp20260919
  acmEntrypoint
  acmInterfaceFailureOutcome
  "ChatGPT web retrieval environment; exact ACM translation available, live search-result retrieval inaccessible"
  "attempt receipt only: no observed result page, count, export, deduplication, screening, eligibility or evidence payment is created"

ieeeQ1Execution = ieeeInterfaceFailureExecution Queries.ieeeQ1DigitalEducationESD
ieeeQ2Execution = ieeeInterfaceFailureExecution Queries.ieeeQ2Transformation
ieeeQ3Execution = ieeeInterfaceFailureExecution Queries.ieeeQ3ReflexiveSustainability
ieeeQ4Execution = ieeeInterfaceFailureExecution Queries.ieeeQ4LifecycleCircularity
ieeeQ5Execution = ieeeInterfaceFailureExecution Queries.ieeeQ5ParticipantGovernance
ieeeQ6Execution = ieeeInterfaceFailureExecution Queries.ieeeQ6LongitudinalInstitutional
ieeeQ7Execution = ieeeInterfaceFailureExecution Queries.ieeeQ7OpenInteroperableRepairable

acmQ1Execution = acmInterfaceFailureExecution Queries.acmQ1DigitalEducationESD
acmQ2Execution = acmInterfaceFailureExecution Queries.acmQ2Transformation
acmQ3Execution = acmInterfaceFailureExecution Queries.acmQ3ReflexiveSustainability
acmQ4Execution = acmInterfaceFailureExecution Queries.acmQ4LifecycleCircularity
acmQ5Execution = acmInterfaceFailureExecution Queries.acmQ5ParticipantGovernance
acmQ6Execution = acmInterfaceFailureExecution Queries.acmQ6LongitudinalInstitutional
acmQ7Execution = acmInterfaceFailureExecution Queries.acmQ7OpenInteroperableRepairable

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
  ∷ ericQ1Execution
  ∷ ericQ2Execution
  ∷ ericQ3Execution
  ∷ ericQ4Execution
  ∷ ericQ5Execution
  ∷ ericQ6Execution
  ∷ ericQ7Execution
  ∷ ieeeQ1Execution
  ∷ ieeeQ2Execution
  ∷ ieeeQ3Execution
  ∷ ieeeQ4Execution
  ∷ ieeeQ5Execution
  ∷ ieeeQ6Execution
  ∷ ieeeQ7Execution
  ∷ acmQ1Execution
  ∷ acmQ2Execution
  ∷ acmQ3Execution
  ∷ acmQ4Execution
  ∷ acmQ5Execution
  ∷ acmQ6Execution
  ∷ acmQ7Execution
  ∷ []

executionReceiptCount : Nat
executionReceiptCount = 35

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
    successfulExecutionMayRecordSubmittedQuery : Bool
    successfulExecutionMayRecordSubmittedQueryIsTrue :
      successfulExecutionMayRecordSubmittedQuery ≡ true
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
  true refl
  false refl

executionReceiptReading : String
executionReceiptReading =
  "All thirty-five frozen translated queries now carry explicit execution-attempt receipts. Scopus/Web of Science were blocked before submission by HTTP 403; ERIC direct API response retrieval was unavailable in the current transport; IEEE Xplore and ACM Digital Library live search-result pages were likewise inaccessible through the current web transport. All outcomes remain pre-result failures and therefore carry no observed result counts or exports. querySubmitted remains a retained coordinate so a future successful execution can record true together with executedWithObservedResultSet, exact translated query, count, result-set identity/export state and execution evidence."
