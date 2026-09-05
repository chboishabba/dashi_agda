module DASHI.Interop.KagentiRabbitMQRuntimeAdapterExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.ContentAddressedTransitionIdentityExact as Identity
import DASHI.Core.RuntimeEventExecutionBridgeExact as Runtime

------------------------------------------------------------------------
-- KAGENTI-NATIVE RABBITMQ ADAPTER CONTRACT
--
-- Source-bounded to the architecture supplied in the collaboration notes:
-- fanout exchange `kagenti.events`, queue `kagenti.agent.events`, and tagged
-- Created / Updated / Deleted AgentEvent messages consumed by a reconciler.
-- This module proves the adapter mapping only; it does not claim broker delivery
-- or systemd/Nix success without a runtime acknowledgement receipt.
------------------------------------------------------------------------

data AgentTransition : Set where
  createAgent updateAgent deleteAgent : AgentTransition

data KagentiAgentEventKind : Set where
  Created Updated Deleted : KagentiAgentEventKind

transitionFor : KagentiAgentEventKind → AgentTransition
transitionFor Created = createAgent
transitionFor Updated = updateAgent
transitionFor Deleted = deleteAgent

runtimeKindFor : KagentiAgentEventKind → Runtime.RuntimeEventKind
runtimeKindFor Created = Runtime.created
runtimeKindFor Updated = Runtime.updated
runtimeKindFor Deleted = Runtime.deleted

record KagentiAgentRuntime : Set where
  constructor kagenti-agent-runtime
  field
    kind : KagentiAgentEventKind
    name : String
    namespace : String
    canonicalPayloadReference : String
    transitionDigest : String
    proofReceiptId : String
    authorityReceiptId : String

open KagentiAgentRuntime public

addressFor : KagentiAgentRuntime → Identity.ContentAddressReceipt
addressFor runtime =
  Identity.content-address-receipt
    "RFC8785-like sorted compact JSON subset used by the reference producer; exact script version recorded externally"
    "sha256"
    (transitionDigest runtime)
    (canonicalPayloadReference runtime)

identityFor :
  (runtime : KagentiAgentRuntime) →
  Identity.SameTransitionSpine (transitionFor (kind runtime))
identityFor runtime =
  Identity.canonicalSpine
    (transitionFor (kind runtime))
    (addressFor runtime)
    "same Kagenti AgentTransition from certification through emitted event"

compileRuntimeEvent :
  (runtime : KagentiAgentRuntime) →
  Runtime.RuntimeEvent (transitionFor (kind runtime))
compileRuntimeEvent runtime =
  Runtime.runtime-event
    (identityFor runtime)
    (runtimeKindFor (kind runtime))
    (namespace runtime)
    (name runtime)
    (canonicalPayloadReference runtime)
    (proofReceiptId runtime)
    (authorityReceiptId runtime)
    (transitionFor (kind runtime))
    refl
    "kagenti.events"
    "kagenti.agent.events"
    "kagenti AgentEvent JSON envelope"

record KagentiRabbitMQAdapterBoundary : Set where
  constructor kagenti-rabbitmq-adapter-boundary
  field
    emittedEventProvesRabbitMQDelivery : Bool
    emittedEventProvesRabbitMQDeliveryIsFalse :
      emittedEventProvesRabbitMQDelivery ≡ false

    rabbitMQDeliveryProvesReconcilerSuccess : Bool
    rabbitMQDeliveryProvesReconcilerSuccessIsFalse :
      rabbitMQDeliveryProvesReconcilerSuccess ≡ false

    reconcilerReceiptProvesNixBuildSuccessWithoutBuildEvidence : Bool
    reconcilerReceiptProvesNixBuildSuccessWithoutBuildEvidenceIsFalse :
      reconcilerReceiptProvesNixBuildSuccessWithoutBuildEvidence ≡ false

    systemdStartRequestProvesRunningAgent : Bool
    systemdStartRequestProvesRunningAgentIsFalse :
      systemdStartRequestProvesRunningAgent ≡ false

canonicalKagentiRabbitMQAdapterBoundary : KagentiRabbitMQAdapterBoundary
canonicalKagentiRabbitMQAdapterBoundary =
  kagenti-rabbitmq-adapter-boundary
    false refl
    false refl
    false refl
    false refl
