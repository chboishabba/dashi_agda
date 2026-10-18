# Self-Hosted Agent Broker Design

## Purpose

Formalise a thin, self-hosted control-plane architecture for supervising long-running heterogeneous agents from a mobile/voice client without making the broker own agent execution, model inference, repositories, network transport, speech, notification delivery, or persistence.

The central architectural rule is:

```text
broker owns coordination semantics, not execution.
```

The motivating use case is ambient supervision while the user is away from a terminal: start or resume jobs, receive compressed status, answer questions, approve/reject actions, interrupt or redirect work, and hear summaries through headphones. The formal object is not a new agent framework; it is a protocol and consumer-adequacy boundary between arbitrary agents and arbitrary human-facing clients.

## Existing machinery to reuse

This tranche must reuse repository-native machinery rather than define parallel calculi:

- `DASHI.Core.PortableSemanticInterpretationExact` for consumer/query-indexed semantic equivalence across replaceable backends;
- `DASHI.Core.QueryFactorisationSufficiency` / canonical `FactorsThrough` machinery for sufficiency and non-factorability claims;
- `DASHI.Core.ConsumerFibreRepairExact` and related consumer-repair machinery where a missing coordinate must be added to repair an insufficient projection;
- existing provenance/evidence-status conventions for distinguishing a formal architectural fixture from runtime/build/certification receipts.

The broker theory should therefore expose semantic contracts and finite witnesses, not duplicate transport, scheduler, notification, or speech implementations.

## Core protocol owner

Create:

`DASHI/ComputerScience/AgentBrokerProtocolExact.agda`

The owner should define a minimal reusable family for:

- `AgentSession`;
- `AgentEvent`;
- `HumanCommand`;
- `AttentionPolicy`;
- adapter-produced observations;
- broker-visible session state;
- consumer queries over broker state.

The canonical event vocabulary should remain small and execution-agnostic. A suitable finite fixture is:

```text
Started
Progress
NeedsInput
NeedsApproval
Blocked
Completed
Failed
ArtifactReady
```

Likewise the canonical control vocabulary should remain execution-agnostic:

```text
Answer
Approve
Reject
Interrupt
Pause
Resume
Cancel
```

The formal protocol must not require a particular model provider, runtime, terminal protocol, repository host, overlay network, message bus, mobile platform, speech stack, push provider, or database.

## Adapter boundary

Agent-specific integrations are adapters into the canonical protocol.

Conceptually:

```text
AgentRuntimeState --adapter--> BrokerEvent
HumanCommand     --adapter--> AgentRuntimeCommand
```

The adapter is permitted to discard implementation-private detail so long as the declared broker consumer queries remain adequate. This is a direct instance of consumer-indexed semantic interpretation rather than exact implementation identity.

A Codex adapter, Claude Code adapter, OpenCode adapter, local script adapter, or future agent implementation must therefore be replaceable without changing the broker protocol semantics.

## BYO independence owner

Create:

`DASHI/ComputerScience/AgentBrokerBYOIndependenceExact.agda`

This owner should construct finite collision witnesses showing that broker semantics do not factor through any one replaceable implementation coordinate.

At minimum establish independent non-factorability claims for:

```text
ModelBackend
ExecutionRuntime
ExecutionMachine
RepositoryBackend
NetworkTransport
SpeechBackend
NotificationBackend
PersistenceBackend
```

The intended theorem shape is:

```text
BrokerConsumerOutcome does not factor through ModelBackend
BrokerConsumerOutcome does not factor through ExecutionRuntime
...
```

The converse implementation-identity implications must also remain unavailable. In particular:

```text
same broker-observable semantics != same model
same broker-observable semantics != same runtime
same broker-observable semantics != same network
same broker-observable semantics != same speech stack
same broker-observable semantics != same persistence implementation
```

These are architectural firewalls, not empirical claims about specific products.

## Attention and interruption owner

Create:

`DASHI/ComputerScience/AgentAttentionBrokerExact.agda`

Raw agent events are not themselves sufficient to determine whether the human should be interrupted.

The intended pipeline is:

```text
raw agent events
  -> session reducer
  -> broker-visible state
  -> attention policy
  -> human notification decision
```

Construct a finite collision proving:

```text
HumanInterruptionDecision
  does not factor through
RawEventKind
```

For example, two sessions may emit the same `Progress` or `Failed` event while differing in whether the user asked to be interrupted for that class of event.

The repair should require a joined observer at least as strong as:

```text
AgentEvent x SessionState x AttentionPolicy
  -> NotifyDecision
```

This owner should distinguish:

- event occurrence;
- event importance;
- interruption eligibility;
- spoken/text summary rendering.

A summariser may be deterministic or model-backed, but summary generation is downstream of the attention decision and is not part of the broker's execution authority.

## Human command and approval boundary

Human commands must remain distinct from agent events.

The protocol should preserve at least these separations:

```text
agent asks for approval != approval granted
agent reports completion != human accepts result
notification delivered != command acknowledged
spoken transcription != authorised control action
```

Where useful, finite non-factorability fixtures should prove that an observation such as "approval requested" cannot determine "approval granted" without a separate human-command coordinate.

This is especially important for voice interfaces where STT output is only an input candidate until it is mapped to an authorised command under the current session/decision context.

## Reference architecture fixture

Create:

`DASHI/ComputerScience/SelfHostedAgentBrokerReferenceArchitectureExact.agda`

This module is a replaceable architectural fixture, not a requirement surface.

Representative witnesses may include:

```text
Overlay network: Headscale/WireGuard
Event transport: NATS or WebSocket
Agent adapters: Codex / Claude Code / OpenCode / arbitrary process adapter
Speech: operating-system STT/TTS or local replacement
Notifications: direct stream / ntfy / Gotify / UnifiedPush / platform push
Persistence: local database / append-only log / other self-hosted store
```

The module must make explicit that these names are examples of inhabitants of implementation coordinates. No theorem may depend on Headscale, NATS, Android, iOS, Codex, Claude Code, or any named provider being the unique implementation.

## Mobile/headphone consumer

The phone/headphone surface is a consumer of the generic broker rather than part of the core protocol.

Its minimal observation should support questions such as:

```text
which sessions are running?
which sessions require attention?
what changed since my last cursor?
what decision is required?
what is the compressed status summary?
```

Its command surface should support:

```text
answer
approve/reject
defer
interrupt
pause/resume
cancel
set attention policy
```

The client may use local OS speech APIs, local speech models, remote speech services, text-only interaction, or no voice at all. Voice capability is therefore consumer presentation, not broker identity.

## Delivery and background execution boundary

Delivery reliability and push/wake behaviour must remain separate from broker semantics.

A broker event being durable does not imply that a phone notification was delivered, and a delivered notification does not imply that the user heard or acknowledged it.

The formal surface should therefore distinguish at least:

```text
EventCommitted
NotificationEligible
NotificationDelivered
HumanAcknowledged
CommandAccepted
```

The reference fixture may mention direct Headscale-connected streaming, UnifiedPush, ntfy, Gotify, FCM, or APNs, but these are transport/delivery witnesses only.

## Provenance and authority

The generic broker architecture, finite collision witnesses, and reference decomposition are DASHI synthesis.

Named technologies in the reference fixture are implementation examples, not mathematical authorities and not proof of production suitability. External product documentation, if later acquired, may support a capability/source atlas but must not be imported as theorem authority.

Runtime observations, integration tests, source-level checks, kernel/type-check receipts, and deployed-system evidence remain separate status coordinates.

## Validation

Follow repository RED-first practice.

A regression surface should require at minimum:

- core protocol event/command/session owners;
- adapter-to-broker semantic contract;
- model/backend non-factorability;
- runtime/backend non-factorability;
- transport/speech/notification/persistence independence;
- raw-event-kind insufficiency for interruption decisions;
- repaired attention observer using session state plus attention policy;
- approval-request versus approval-grant separation;
- reference fixture proving named technologies inhabit replaceable coordinates only.

Do not claim runtime integration, mobile delivery, external-agent compatibility, Agda kernel certification, or deployed self-hosting unless corresponding receipts are actually observed.

## Non-goals

This tranche does not implement:

- a new agent planner;
- a scheduler for agent internals;
- an LLM provider abstraction beyond what the broker consumer needs;
- a mobile application;
- Headscale, NATS, WebSocket, push, STT, or TTS clients;
- a production authentication/authorisation system;
- exact operational semantics for Codex, Claude Code, OpenCode, or any external agent.

Those are downstream implementation projects that may instantiate this formal contract.

## Success criterion

The formalisation is successful when DASHI can express and prove, without tying itself to a particular implementation stack, that:

```text
many heterogeneous agent implementations
  -> adapters
  -> one consumer-adequate broker protocol
  -> attention-policy-controlled human supervision
```

while retaining the central firewall:

```text
coordination authority != execution ownership.
```
