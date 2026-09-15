# Portable Semantic Interpretation Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Add a repo-native semantic-refinement parent theory plus UI and loop child instances showing that different backends may preserve the same consumer-relevant meaning without implementation identity.

**Architecture:** Introduce `PortableSemanticInterpretationExact` as the generic parent. It exposes syntax, meaning, backend-specific implementation, consumer query, and query-indexed observation/refinement. `PortableInteractiveViewExact` and `PortableLoopInterpretationExact` instantiate that surface; a small MDL bridge reuses existing admissibility/consumer-adequacy machinery rather than creating a parallel ranking calculus.

**Tech Stack:** Agda, existing DASHI Core abstractions, shell/source regression checks only; no CI invocation.

**Spec:** `docs/superpowers/specs/2026-09-15-portable-semantic-interpretation-design.md`

## Global Constraints

- Semantic equality is consumer/query indexed; do not require backend implementation equality.
- Same semantics must not imply same syntax, algorithm, execution order, performance, memory behaviour, or pixels.
- Keep UI framework events distinct from domain commands.
- Treat GPU/render details as optional child metadata, not parent semantic authority.
- Reuse `DASHI.Core.AdmissibleConsumerMDLHyperfabricExact` for adequacy/Pareto integration.
- Reuse `DASHI.Core.GenericFuturePartitionRefinementExact` where finite action traces are needed; do not duplicate it.
- Generic architecture and finite fixtures are DASHI synthesis; preserve existing attribution boundaries.
- RED-first regression surfaces; do not invoke CI.

---

### Task 1: Parent query-indexed semantic interpretation owner

**Files:**
- Create: `DASHI/Core/PortableSemanticInterpretationRegression.agda`
- Create: `DASHI/Core/PortableSemanticInterpretationExact.agda`

**Interfaces:**
- Consumes: `DASHI.Core.Prelude` and ordinary Agda equality/product primitives.
- Produces:
  - `SemanticInterpretationProblem`
  - `SemanticRefinement`
  - `BackendEquivalentFor`
  - `twoRefinementsGiveConsumerEquivalence`
  - `PortableSemanticInterpretationBoundary`

- [ ] **Step 1: Write the failing regression**

Create a regression that imports the not-yet-existing owner and requires the public surface:

```agda
module DASHI.Core.PortableSemanticInterpretationRegression where

import DASHI.Core.PortableSemanticInterpretationExact as Portable

problemSurfaceExists : Set₁
problemSurfaceExists = Portable.SemanticInterpretationProblem

refinementSurfaceExists :
  (problem : Portable.SemanticInterpretationProblem) → Set₁
refinementSurfaceExists problem = Portable.SemanticRefinement problem
```

Also require a canonical boundary value so the regression fixes the intended firewalls.

- [ ] **Step 2: Verify RED**

Run the repository's normal narrow Agda/source check for the regression module, or compile it directly using the repo's configured Agda include path. Expected result: failure because `DASHI.Core.PortableSemanticInterpretationExact` does not yet exist. Record only the observed failure mode.

- [ ] **Step 3: Implement the minimal parent owner**

Use a dependent backend implementation family so backend-specific carriers remain distinct:

```agda
record SemanticInterpretationProblem : Set₁ where
  field
    Syntax : Set
    Meaning : Set
    Backend : Set
    Implementation : Backend → Set
    Query : Set
    Observation : Query → Set
    meaning : Syntax → Meaning
    observeMeaning : (query : Query) → Meaning → Observation query
    interpret : (backend : Backend) → Syntax → Implementation backend
    observeImplementation :
      (backend : Backend) →
      (query : Query) →
      Implementation backend →
      Observation query
```

Define semantic refinement as the backend observation matching the semantic observation for one syntax/query pair:

```agda
record SemanticRefinement
    (problem : SemanticInterpretationProblem) : Set₁ where
  field
    backend : Backend problem
    syntax : Syntax problem
    query : Query problem
    preservesObservation :
      observeImplementation problem backend query
        (interpret problem backend syntax)
      ≡
      observeMeaning problem query (meaning problem syntax)
```

Define `BackendEquivalentFor problem syntax query left right` as equality of the two observed implementation results, then prove `twoRefinementsGiveConsumerEquivalence` by transitivity through semantic meaning.

Add a boundary record with explicit `false` fields for implications from same semantics to same syntax/algorithm/execution order/performance/memory behaviour/pixels.

- [ ] **Step 4: Verify GREEN**

Compile or source-check both parent and regression modules. Expected: the regression surface is satisfied and the boundary fixture typechecks.

- [ ] **Step 5: Commit**

Commit the parent owner and regression as one independently reviewable tranche.

---

### Task 2: Portable interactive view child instance

**Files:**
- Create: `DASHI/Core/PortableInteractiveViewRegression.agda`
- Create: `DASHI/Core/PortableInteractiveViewExact.agda`

**Interfaces:**
- Consumes: `PortableSemanticInterpretationExact`.
- Produces:
  - small declarative `UiNode Command` algebra;
  - framework-neutral `Interaction` carrier;
  - `view`, `interact`, and `reduce` loop fixture;
  - `activationEmitsAttachedCommand`;
  - one parent `SemanticRefinement` witness for a canonical frontend backend.

- [ ] **Step 1: Write the failing regression**

Require the child theorem before the implementation exists:

```agda
module DASHI.Core.PortableInteractiveViewRegression where

import DASHI.Core.PortableInteractiveViewExact as UI

activationContractExists : Set
activationContractExists = UI.ActivationContract

canonicalActivationPaid : UI.ActivationContract
canonicalActivationPaid = UI.canonicalActivationContract
```

- [ ] **Step 2: Verify RED**

Run the narrow source/Agda check. Expected: missing child module.

- [ ] **Step 3: Implement the UI algebra**

Keep the algebra finite and framework neutral. Use a simple inductive node family such as:

```agda
data UiNode (Command : Set) : Set where
  text : String → UiNode Command
  box : UiNode Command → Maybe Command → UiNode Command
  row : List (UiNode Command) → UiNode Command
  column : List (UiNode Command) → UiNode Command
  button : String → Command → UiNode Command
  canvas : String → UiNode Command
```

Use a minimal interaction carrier that can express activation of a node in the finite fixture. The canonical theorem must state that activating a node carrying `command` emits that same domain command; it must not speak about pixels, exact bounds, WebGPU, or framework event structs.

Instantiate the parent semantic interpretation with two frontend tags whose implementation metadata differs but whose command-emission observation agrees for the canonical activation query.

- [ ] **Step 4: Verify GREEN**

Compile/source-check the child and regression. Confirm the canonical parent refinement witness and activation theorem are available.

- [ ] **Step 5: Commit**

Commit the UI child instance and regression.

---

### Task 3: Sequential versus parallel loop child instance

**Files:**
- Create: `DASHI/Core/PortableLoopInterpretationRegression.agda`
- Create: `DASHI/Core/PortableLoopInterpretationExact.agda`

**Interfaces:**
- Consumes: `PortableSemanticInterpretationExact` and repo finite-list primitives.
- Produces:
  - exact finite `LoopIntent` fixture;
  - backend tags `jsSequential` and `gpuParallel` (names describe implementation roles only);
  - distinct implementation metadata;
  - shared consumer query observing final logical result;
  - `jsAndGpuEquivalentForResult` derived through parent refinement.

- [ ] **Step 1: Write the failing regression**

Require the exact cross-backend result theorem:

```agda
module DASHI.Core.PortableLoopInterpretationRegression where

import DASHI.Core.PortableLoopInterpretationExact as Loop

loopEquivalenceExists : Loop.CanonicalLoopConsumerEquivalence
loopEquivalenceExists = Loop.jsAndGpuEquivalentForResult
```

- [ ] **Step 2: Verify RED**

Run the narrow source/Agda check. Expected: missing loop child module.

- [ ] **Step 3: Implement the exact finite fixture**

Use `Nat`/finite lists and an exact operation such as summation or increment mapping. Give the two backend implementation records different execution metadata, for example sequential versus parallel scheduling tags, while making their observed final logical result equal to the semantic meaning.

Do not formalise JavaScript language semantics or WebGPU operational semantics. The names are role labels for two implementation strategies.

Create two `SemanticRefinement` witnesses and derive `jsAndGpuEquivalentForResult` using `twoRefinementsGiveConsumerEquivalence` rather than proving backend equality directly.

- [ ] **Step 4: Verify GREEN**

Compile/source-check loop owner and regression. Confirm execution metadata remains distinct while final-result observation agrees.

- [ ] **Step 5: Commit**

Commit the loop child instance and regression.

---

### Task 4: Consumer-adequacy bridge and Pareto firewall

**Files:**
- Create: `DASHI/Core/PortableSemanticConsumerAdequacyBridgeExact.agda`
- Create: `DASHI/Core/PortableSemanticConsumerAdequacyRegression.agda`

**Interfaces:**
- Consumes:
  - `PortableSemanticInterpretationExact.SemanticRefinement`
  - `AdmissibleConsumerMDLHyperfabricExact.ConsumerMDLProblem`
- Produces:
  - a small candidate-backend fixture;
  - `ConsumerAdequate` inhabited only when required semantic query refinement is paid;
  - a proof that ranking remains downstream of semantic adequacy.

- [ ] **Step 1: Write the failing regression**

Require one canonical bridge receipt showing an adequate backend candidate is eligible only after both admissibility and semantic-query adequacy are present.

- [ ] **Step 2: Verify RED**

Run the narrow source/Agda check. Expected: missing bridge owner.

- [ ] **Step 3: Implement the bridge**

Instantiate the existing `ConsumerMDLProblem`; do not modify the parent MDL calculus. Let `ConsumerAdequate candidate` be witnessed by a required semantic refinement receipt for the declared query. Use the existing `Eligible = Admissible × ConsumerAdequate` theorem surface to show the candidate enters the ranking stratum only after both gates are paid.

- [ ] **Step 4: Verify GREEN**

Compile/source-check bridge and regression. Confirm no new Pareto relation or cost order has been introduced.

- [ ] **Step 5: Commit**

Commit the adequacy bridge and regression.

---

### Task 5: Core rollup and focused validation surface

**Files:**
- Modify: `DASHI/Core/Everything.agda`
- Create: `scripts/check_portable_semantic_interpretation.sh`

**Interfaces:**
- Consumes all four earlier tasks.
- Produces one focused local validation entrypoint and exports the new reusable core owners through the normal core rollup.

- [ ] **Step 1: Add the imports to `DASHI/Core/Everything.agda`**

Add imports for:

```text
DASHI.Core.PortableSemanticInterpretationExact
DASHI.Core.PortableInteractiveViewExact
DASHI.Core.PortableLoopInterpretationExact
DASHI.Core.PortableSemanticConsumerAdequacyBridgeExact
```

Place them with the other reusable consumer/refinement core surfaces.

- [ ] **Step 2: Add the focused checker**

Create a shell checker that invokes the repository's available local Agda/source validation on exactly the new owners/regressions and exits non-zero on failure. It must not invoke GitHub Actions or broad CI.

- [ ] **Step 3: Run the focused checker**

Record the exact observed result. Distinguish source presence/checker success from any Agda kernel receipt if the configured Agda toolchain is unavailable.

- [ ] **Step 4: Inspect the diff for scope and attribution**

Verify the tranche contains only the parent theory, two child witnesses, adequacy bridge, focused regression/check surface, spec/plan, and rollup import. Confirm no external framework claims have been promoted into theorem statements.

- [ ] **Step 5: Commit**

Commit rollup/checker integration separately from the semantic owners.

## Self-review

- Spec coverage: parent semantic refinement, UI child, JS/WebGPU-style loop child, consumer-indexed equivalence, adequacy/Pareto reuse, and firewalls are each assigned to a task.
- Placeholder scan: no implementation step depends on unspecified TODO behaviour.
- Type consistency: `SemanticInterpretationProblem`, `SemanticRefinement`, `BackendEquivalentFor`, and `twoRefinementsGiveConsumerEquivalence` are defined in Task 1 and consumed consistently by later tasks.
- Scope: this remains one coherent reusable-core tranche; concrete egui/eframe Rust integration is intentionally excluded and can be a later bridge once this semantic surface exists.
