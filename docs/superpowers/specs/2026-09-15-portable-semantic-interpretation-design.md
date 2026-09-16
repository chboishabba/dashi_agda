# Portable Semantic Interpretation Design

## Purpose

Formalise a high-level architecture in which multiple implementation backends may realise the same consumer-relevant semantics without requiring equality of syntax, execution order, rendering, memory behaviour, or performance.

The motivating examples are deliberately heterogeneous:

- a JavaScript sequential loop and a WebGPU compute loop that implement the same consumer-relevant iteration;
- an egui box and another frontend's retained/widget representation that both mean "show this content and emit command `c` when activated".

The parent theory is therefore about semantic interpretation/refinement, not GPU equivalence and not UI-framework equivalence.

## Core object

Let `Syntax` describe portable intent, `Meaning` describe the semantic object exposed to the consumer, and `Implementation` be backend-specific.

The parent owner will model:

```text
Syntax --meaning--> Meaning
   \
    \--interpret backend--> Implementation --observe query--> Observation
```

Correctness is query-indexed: a backend is adequate when its observed implementation result agrees with the observation demanded by the declared consumer. Exact implementation identity is not required.

Conceptually:

```text
meaning   : Syntax -> Meaning
interpret : Backend -> Syntax -> Implementation Backend
observe   : Query -> Meaning -> Observation Query
observeImplementation : Backend -> Query -> Implementation Backend -> Observation Query
```

A semantic-refinement witness states that, for a declared query and syntax object, the backend observation matches the semantic observation.

## Consumer-indexed equivalence

Two backends are equivalent only relative to the declared consumer/query. This permits a JavaScript loop and WebGPU loop to be equivalent for a mathematical result query while differing in scheduling, parallelism, intermediate floating-point order, memory traffic, and cost.

Likewise two UI backends may be equivalent for a command-emission query while differing in pixels, text metrics, layout implementation, retained/immediate mode, or native widget/event representation.

The parent theorem must therefore avoid raw implementation equality.

## Parent owner

Create:

`DASHI/Core/PortableSemanticInterpretationExact.agda`

The owner should provide a small reusable record surface for:

- portable syntax/intent;
- semantic meaning;
- backend family;
- backend-specific implementation carrier;
- consumer query and query result;
- semantic observation;
- backend observation;
- query-indexed semantic-refinement witnesses;
- cross-backend equivalence derived from two refinement witnesses.

The file should reuse repo-native finite-trace/refinement and consumer-adequacy ideas where useful, but not duplicate `AdmissibleConsumerMDLHyperfabricExact` or `GenericFuturePartitionRefinementExact`.

## Child instance: portable interactive view

Create:

`DASHI/Core/PortableInteractiveViewExact.agda`

This is a concrete child instance of the parent theory. Its high-level UI algebra is intentionally small:

```text
Text content
Box child optional-command
Row children
Column children
Button label command
Canvas render-key
```

The core loop is:

```text
State --view--> UI(Command)
UI(Command) + Interaction --interact--> List Command
State + Command --reduce--> State
```

The semantic obligations are interaction-level rather than pixel-level. The canonical witness should express that activating a node carrying command `c` emits `c`.

The owner should keep framework events distinct from domain commands. It should not formalise exact pixels, exact layout, exact text metrics, or exact GPU behaviour.

## Child instance: loop interpretation

Create:

`DASHI/Core/PortableLoopInterpretationExact.agda`

This child demonstrates that a sequential loop backend and a parallel/backend-dispatch interpretation can share a consumer-relevant loop meaning.

The canonical finite fixture should avoid floating-point complications and use an exact finite data type, so the formal theorem is genuinely exact. It should model one loop intent, two implementation tags (for example `jsSequential` and `gpuParallel`), and one consumer query that observes the final logical result. The backend implementations may differ in execution metadata while producing the same observed result.

This file is a semantic witness, not a claim that JavaScript and WebGPU have identical operational semantics.

## Pareto and adequacy integration

Framework/backend ranking remains downstream.

`AdmissibleConsumerMDLHyperfabricExact` already establishes that ranking occurs only after admissibility and consumer adequacy. This design should therefore expose a bridge or fixture showing how semantic-refinement evidence can discharge a `ConsumerAdequate` obligation for a candidate backend, without adding a second Pareto calculus.

The following must remain false as architectural implications:

```text
same semantics -> same syntax
same semantics -> same algorithm
same semantics -> same execution order
same semantics -> same performance
same semantics -> same memory behaviour
same semantics -> same pixels
```

## Attribution

The generic semantic-refinement architecture and finite fixtures are DASHI synthesis. Existing repo modules reused by the design retain their own attribution/source boundaries. No external UI/GPU framework documentation is promoted into mathematical authority by this tranche.

## Validation

Use RED-first regression surfaces following repository practice. The regression should require:

- the parent query-indexed refinement witness;
- cross-backend consumer equivalence;
- the interactive activation-to-command theorem;
- the loop cross-backend observed-result theorem;
- the downstream consumer-adequacy bridge.

Do not invoke CI. Source-level validation should be reported separately from any kernel/build receipt actually observed.
