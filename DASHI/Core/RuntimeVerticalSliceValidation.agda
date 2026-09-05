module DASHI.Core.RuntimeVerticalSliceValidation where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Core.ContentAddressedTransitionIdentityExact as Identity
import DASHI.Core.RuntimeEventExecutionBridgeExact as Runtime
import DASHI.Core.RuntimeFeedbackSelectiveReopeningExact as Reopen
import DASHI.Core.AffectedDependencyClosureExact as Closure
import DASHI.Interop.KagentiRabbitMQRuntimeAdapterExact as Kagenti

------------------------------------------------------------------------
-- Canonical same-object runtime event regression.
------------------------------------------------------------------------

createdRuntime : Kagenti.KagentiAgentRuntime
createdRuntime =
  Kagenti.kagenti-agent-runtime
    Kagenti.Created
    "hello"
    "monster"
    "Fixtures/Runtime/kagenti_agent_created.json"
    "fixture-transition-sha256"
    "proof-demo-001"
    "authority-demo-001"

createdEvent : Runtime.RuntimeEvent Kagenti.createAgent
createdEvent = Kagenti.compileRuntimeEvent createdRuntime

createdEventLiteralTransitionIsCreateAgent :
  Runtime.emittedTransition createdEvent ≡ Kagenti.createAgent
createdEventLiteralTransitionIsCreateAgent =
  Runtime.emittedTransitionExact createdEvent

createdExecutionAck : Runtime.RuntimeExecutionAck Kagenti.createAgent createdEvent
createdExecutionAck =
  Runtime.runtime-execution-ack
    Kagenti.createAgent
    refl
    Runtime.runtimeExecuted
    "deterministic-local-reference-executor"
    "agent inserted into reference runtime state"
    "Fixtures/Runtime generated execution receipt"

createdFeedback :
  Runtime.RuntimeFeedbackReceipt Kagenti.createAgent createdEvent createdExecutionAck
createdFeedback =
  Runtime.runtime-feedback-receipt
    "empty agent runtime state"
    "runtime state containing monster/hello"
    "after-state digest observed by verifier"
    "monster/hello"
    "RabbitMQ/Nix/systemd external execution remains unresolved"
    "reference-runtime feedback receipt"

------------------------------------------------------------------------
-- Transitive reopening regression.
------------------------------------------------------------------------

data Artifact : Set where
  observation certificate decision : Artifact

data Depends : Artifact → Artifact → Set where
  observationCertificate : Depends observation certificate
  certificateDecision : Depends certificate decision

observationReopensDecision :
  Closure.ReopeningObligation Depends observation decision
observationReopensDecision =
  Closure.reopeningObligation
    (Closure.affectedStep
      observationCertificate
      (Closure.affectedStep certificateDecision Closure.affectedRefl))

reopenDecision : Reopen.ReopenTarget Depends observation
reopenDecision =
  Reopen.reopen-target
    decision
    observationReopensDecision
    "runtime observation transitively reopens decision certificate"

------------------------------------------------------------------------
-- Main boundary regressions.
------------------------------------------------------------------------

runtimeEmissionDoesNotProveExecution :
  Runtime.emittedEventAutomaticallyProvesExecution
    Runtime.canonicalRuntimeEventExecutionBoundary
  ≡ false
runtimeEmissionDoesNotProveExecution =
  Runtime.emittedEventAutomaticallyProvesExecutionIsFalse
    Runtime.canonicalRuntimeEventExecutionBoundary

sameDigestDoesNotProveSemanticEquality :
  Identity.sameDigestAutomaticallyProvesSemanticEquality
    Identity.canonicalTransitionIdentityBoundary
  ≡ false
sameDigestDoesNotProveSemanticEquality =
  Identity.sameDigestAutomaticallyProvesSemanticEqualityIsFalse
    Identity.canonicalTransitionIdentityBoundary

rabbitDeliveryDoesNotProveReconcilerSuccess :
  Kagenti.rabbitMQDeliveryProvesReconcilerSuccess
    Kagenti.canonicalKagentiRabbitMQAdapterBoundary
  ≡ false
rabbitDeliveryDoesNotProveReconcilerSuccess =
  Kagenti.rabbitMQDeliveryProvesReconcilerSuccessIsFalse
    Kagenti.canonicalKagentiRabbitMQAdapterBoundary
