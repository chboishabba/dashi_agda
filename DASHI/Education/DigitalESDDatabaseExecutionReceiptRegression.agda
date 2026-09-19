module DASHI.Education.DigitalESDDatabaseExecutionReceiptRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Education.DigitalESDDatabaseExecutionReceiptExact as Exec
import DASHI.Education.DigitalESDDatabaseTranslatedQueriesExact as Queries

executionReceiptCountRegression : Exec.executionReceiptCount ≡ 42
executionReceiptCountRegression = refl

scopusExecutionAttemptedRegression :
  Exec.DatabaseExecutionReceipt.executionAttempted Exec.scopusQ1Execution ≡ true
scopusExecutionAttemptedRegression = refl

wosExecutionAttemptedRegression :
  Exec.DatabaseExecutionReceipt.executionAttempted Exec.wosQ1Execution ≡ true
wosExecutionAttemptedRegression = refl

scopusCurrentQueryNotSubmittedRegression :
  Exec.DatabaseExecutionReceipt.querySubmitted Exec.scopusQ1Execution ≡ false
scopusCurrentQueryNotSubmittedRegression = refl

wosCurrentQueryNotSubmittedRegression :
  Exec.DatabaseExecutionReceipt.querySubmitted Exec.wosQ1Execution ≡ false
wosCurrentQueryNotSubmittedRegression = refl

scopusBlockedBeforeSubmissionRegression :
  Exec.DatabaseExecutionReceipt.outcome Exec.scopusQ1Execution
  ≡ Exec.accessBlockedBeforeSubmission "HTTP 403 at Scopus Advanced Search entrypoint in this execution environment"
scopusBlockedBeforeSubmissionRegression = refl

wosBlockedBeforeSubmissionRegression :
  Exec.DatabaseExecutionReceipt.outcome Exec.wosQ1Execution
  ≡ Exec.accessBlockedBeforeSubmission "HTTP 403 at Web of Science Core Collection entrypoint in this execution environment"
wosBlockedBeforeSubmissionRegression = refl

translatedQueryIdentityRegression :
  Exec.DatabaseExecutionReceipt.translatedQuery Exec.scopusQ1Execution
  ≡ Queries.scopusQ1DigitalEducationESD
translatedQueryIdentityRegression = refl

futureSubmittedExecutionPermittedRegression :
  Exec.DatabaseExecutionBoundary.successfulExecutionMayRecordSubmittedQuery
    Exec.canonicalDatabaseExecutionBoundary
  ≡ true
futureSubmittedExecutionPermittedRegression = refl

blockedExecutionCannotCreateObservedResultCountRegression :
  Exec.BlockedExecutionCreatesObservedResultCount → ⊥
blockedExecutionCannotCreateObservedResultCountRegression =
  Exec.blockedExecutionDoesNotCreateObservedResultCount

blockedExecutionCannotCreateExportRegression :
  Exec.BlockedExecutionCreatesExport → ⊥
blockedExecutionCannotCreateExportRegression =
  Exec.blockedExecutionDoesNotCreateExport

blockedExecutionCannotCreateIncludedCorpusRegression :
  Exec.ExecutionReceiptCreatesIncludedCorpus → ⊥
blockedExecutionCannotCreateIncludedCorpusRegression =
  Exec.executionReceiptDoesNotCreateIncludedCorpus


ericExecutionAttemptedRegression :
  Exec.DatabaseExecutionReceipt.executionAttempted Exec.ericQ1Execution ≡ true
ericExecutionAttemptedRegression = refl

ericCurrentQueryNotSubmittedRegression :
  Exec.DatabaseExecutionReceipt.querySubmitted Exec.ericQ1Execution ≡ false
ericCurrentQueryNotSubmittedRegression = refl

ericInterfaceFailureBeforeSubmissionRegression :
  Exec.DatabaseExecutionReceipt.outcome Exec.ericQ1Execution
  ≡ Exec.interfaceFailureBeforeSubmission
      "current web transport refused direct api.ies.ed.gov access before a result response could be observed"
ericInterfaceFailureBeforeSubmissionRegression = refl

ericTranslatedQueryIdentityRegression :
  Exec.DatabaseExecutionReceipt.translatedQuery Exec.ericQ1Execution
  ≡ Queries.ericQ1DigitalEducationESD
ericTranslatedQueryIdentityRegression = refl


ieeeExecutionAttemptedRegression :
  Exec.DatabaseExecutionReceipt.executionAttempted Exec.ieeeQ1Execution ≡ true
ieeeExecutionAttemptedRegression = refl

acmExecutionAttemptedRegression :
  Exec.DatabaseExecutionReceipt.executionAttempted Exec.acmQ1Execution ≡ true
acmExecutionAttemptedRegression = refl

ieeeInterfaceFailureBeforeSubmissionRegression :
  Exec.DatabaseExecutionReceipt.outcome Exec.ieeeQ1Execution
  ≡ Exec.interfaceFailureBeforeSubmission
      "current web transport could not retrieve an IEEE Xplore search-result page for the query-bearing URL"
ieeeInterfaceFailureBeforeSubmissionRegression = refl

acmInterfaceFailureBeforeSubmissionRegression :
  Exec.DatabaseExecutionReceipt.outcome Exec.acmQ1Execution
  ≡ Exec.interfaceFailureBeforeSubmission
      "current web transport could not retrieve an ACM Digital Library search-result page for the query-bearing URL"
acmInterfaceFailureBeforeSubmissionRegression = refl


ericObservedQ1SubmittedRegression :
  Exec.DatabaseExecutionReceipt.querySubmitted Exec.ericQ1ObservedExecution ≡ true
ericObservedQ1SubmittedRegression = refl

ericObservedQ1CountRegression :
  Exec.DatabaseExecutionReceipt.outcome Exec.ericQ1ObservedExecution
  ≡ Exec.executedWithObservedResultSet
      642
      "ERIC Q1 live JSON result set observed from official public API"
      (Exec.exportNotObserved
        "count-only probe observed; paginated JSON/CSV export not yet retained")
      "HTTP 200; numFound=642"
ericObservedQ1CountRegression = refl

ericObservedQ7CountRegression :
  Exec.DatabaseExecutionReceipt.outcome Exec.ericQ7ObservedExecution
  ≡ Exec.executedWithObservedResultSet
      1675
      "ERIC Q7 live JSON result set observed from official public API"
      (Exec.exportNotObserved
        "count-only probe observed; paginated JSON/CSV export not yet retained")
      "HTTP 200; numFound=1675"
ericObservedQ7CountRegression = refl
