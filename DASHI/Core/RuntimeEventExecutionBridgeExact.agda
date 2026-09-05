module DASHI.Core.RuntimeEventExecutionBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.ContentAddressedTransitionIdentityExact as Identity

------------------------------------------------------------------------
-- RUNTIME EVENT / EXECUTION / FEEDBACK BRIDGE
------------------------------------------------------------------------

data RuntimeEventKind : Set where
  created updated deleted : RuntimeEventKind

data RuntimeExecutionOutcome : Set where
  runtimeExecuted runtimeRejected runtimePartial : RuntimeExecutionOutcome

record RuntimeEvent {Transition : Set} (canonical : Transition) : Set₁ where
  constructor runtime-event
  field
    identity : Identity.SameTransitionSpine canonical
    kind : RuntimeEventKind
    namespace : String
    name : String
    canonicalPayloadReference : String
    proofReceiptId : String
    authorityReceiptId : String
    emittedTransition : Transition
    emittedTransitionExact : emittedTransition ≡ canonical
    exchangeReference : String
    queueReference : String
    eventReference : String

open RuntimeEvent public

record RuntimeExecutionAck
    {Transition : Set}
    (canonical : Transition)
    (event : RuntimeEvent canonical) : Set₁ where
  constructor runtime-execution-ack
  field
    executedTransition : Transition
    executedTransitionExact : executedTransition ≡ canonical
    outcome : RuntimeExecutionOutcome
    executorReference : String
    externalEffectReference : String
    acknowledgementReference : String

open RuntimeExecutionAck public

record RuntimeFeedbackReceipt
    {Transition : Set}
    (canonical : Transition)
    (event : RuntimeEvent canonical)
    (ack : RuntimeExecutionAck canonical event) : Set₁ where
  constructor runtime-feedback-receipt
  field
    sourceStateReference : String
    resultStateReference : String
    governedObservationReference : String
    changedArtifactReference : String
    residualReference : String
    feedbackReference : String

open RuntimeFeedbackReceipt public

record RuntimeEventExecutionBoundary : Set where
  constructor runtime-event-execution-boundary
  field
    emittedEventAutomaticallyProvesExecution : Bool
    emittedEventAutomaticallyProvesExecutionIsFalse :
      emittedEventAutomaticallyProvesExecution ≡ false

    executionAckAutomaticallyProvesDesiredWorldOutcome : Bool
    executionAckAutomaticallyProvesDesiredWorldOutcomeIsFalse :
      executionAckAutomaticallyProvesDesiredWorldOutcome ≡ false

    partialExecutionMayBeRecordedAsFullExecution : Bool
    partialExecutionMayBeRecordedAsFullExecutionIsFalse :
      partialExecutionMayBeRecordedAsFullExecution ≡ false

    feedbackMayEraseResidualByDefault : Bool
    feedbackMayEraseResidualByDefaultIsFalse :
      feedbackMayEraseResidualByDefault ≡ false

canonicalRuntimeEventExecutionBoundary : RuntimeEventExecutionBoundary
canonicalRuntimeEventExecutionBoundary =
  runtime-event-execution-boundary
    false refl
    false refl
    false refl
    false refl
