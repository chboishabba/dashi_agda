module DASHI.Education.DigitalESDDatabaseExecutionReceiptRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Education.DigitalESDDatabaseExecutionReceiptExact as Exec
import DASHI.Education.DigitalESDDatabaseTranslatedQueriesExact as Queries

executionReceiptCountRegression : Exec.executionReceiptCount ≡ 14
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
