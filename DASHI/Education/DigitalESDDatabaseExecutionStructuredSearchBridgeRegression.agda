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
