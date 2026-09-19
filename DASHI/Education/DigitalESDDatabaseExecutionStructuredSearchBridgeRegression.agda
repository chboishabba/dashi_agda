module DASHI.Education.DigitalESDDatabaseExecutionStructuredSearchBridgeRegression where

open import DASHI.Core.Prelude
open import Data.Empty using (⊥)

import DASHI.Education.DigitalESDDatabaseExecutionReceiptExact as Exec
import DASHI.Education.DigitalESDDatabaseExecutionStructuredSearchBridgeExact as Bridge

scopusBlockedCannotQualify :
  Bridge.SuccessfulObservedOutcome
    (Exec.outcome Exec.scopusQ1Execution) → ⊥
scopusBlockedCannotQualify =
  Bridge.scopusQ1BlockedAttemptCannotCreateSuccessfulOutcome

ericTransportFailureCannotQualify :
  Bridge.SuccessfulObservedOutcome
    (Exec.outcome Exec.ericQ1Execution) → ⊥
ericTransportFailureCannotQualify =
  Bridge.ericQ1TransportFailureCannotCreateSuccessfulOutcome


ericObservedCountWithoutExportCannotQualify :
  Bridge.SuccessfulObservedOutcome
    (Exec.outcome Exec.ericQ1ObservedExecution) → ⊥
ericObservedCountWithoutExportCannotQualify =
  Bridge.ericQ1ObservedCountWithoutExportCannotCreateSuccessfulOutcome

ericExportQ1PassesBridgeRegression :
  Bridge.SuccessfulExecutionForSurface.attempt Bridge.ericQ1SuccessfulExecution
  ≡ Exec.ericQ1ObservedExportExecution
ericExportQ1PassesBridgeRegression = refl

ericExportQ7PassesBridgeRegression :
  Bridge.SuccessfulExecutionForSurface.attempt Bridge.ericQ7SuccessfulExecution
  ≡ Exec.ericQ7ObservedExportExecution
ericExportQ7PassesBridgeRegression = refl

