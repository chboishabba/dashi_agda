# Dioxus + wgpu Hyperfabric v0 Implementation Plan

> **Execution rule:** TDD first. Do not claim GREEN without fresh Rust/Agda receipts. Dioxus is the ordinary application shell; wgpu/WGSL owns all charts and interaction-heavy visualisation. No JSON/regex semantic ABI.

## Goal

Prove the first portable rich-visualisation seam:

```text
canonical semantic state
  -> framework-neutral Visualisation IR
     -> Dioxus shell projection
     -> wgpu visual projection

Dioxus control event ----\
                         -> same admitted DomainCommand -> same reducer
GPU pick ----------------/
```

The retained v0 slice is intentionally small: one tiny interactive 2D chart plus one 3–5 node / 2–4 weighted-edge graph specimen, deterministic static layout, GPU picking, and a Dioxus control that emits the same semantic command as the GPU pick. No production Sankey layout yet.

## Architectural invariants

- `Dioxus != visual semantic authority`.
- `wgpu renderer != canonical graph store`.
- `pi_V` is **not required** to factor through `pi_D`.
- Dioxus and GPU input paths may differ physically while decoding to the same domain command.
- `GpuPick != SemanticMutation` and `DioxusEvent != SemanticMutation`; both are proposals that must pass the same command/admission boundary.
- `HiddenFromVisual != AbsentFromWorld`.
- `RendererEquivalence != PixelEquivalence`.
- `PerformanceWitness != SemanticIdentity`.
- No JSON, NDJSON, JSONL, JSONB, or regex parser in the production semantic/interaction ABI.

## Target repositories

- Formal contract / parity owner: `chboishabba/dashi_agda`, branch `agent/portable-semantic-interpretation`.
- First executable interpreter: `chboishabba/solfunmeme-dioxus`.
- Existing related repositories (`erdfa-publish-rs`, `ipfs-dasl`, `mesh-sync-rs`, `zos-server`, `zkperf`, `zkSEC`, `kant-zk-pastebin`) remain orthogonal publication/transport/conformance/performance/admission lanes and are **not** dependencies of v0 unless an already-existing small type can be reused without expanding scope.

---

## Task 1 — Formalise the visual-interaction contract in DASHI

### Files

Create:
- `DASHI/Interop/PortableInteractiveGpuProjectionExact.agda`
- `DASHI/Interop/DioxusWgpuHyperfabricBridgeExact.agda`

Update:
- the nearest existing aggregate exporting `PortableSemanticInterpretationExact` (do not invent a second aggregate; inspect branch before editing).

### RED first

Add a focused checker/import surface that fails until both new owners exist and export the expected command-decoding witnesses.

### Minimal formal surface

Model:

```text
VisualObjectId
DomainCommand = SelectObject VisualObjectId
ShellInput
GpuPickInput
VisualProjection
ShellProjection
```

Expose two decoding functions/witnesses:

```text
decodeD : ShellInput -> DomainCommand
decodeG : GpuPickInput -> DomainCommand
```

and a v0 parity fixture witnessing:

```text
decodeD shellSelect42 == decodeG gpuPick42 == SelectObject 42
```

Record/firewall fields must include at least:

```text
visualProjectionRequiresShellFactorisation = false
gpuPickCreatesSemanticAuthority = false
dioxusEventCreatesSemanticAuthority = false
hiddenFromVisualMeansAbsentFromWorld = false
rendererParityRequiresPixelParity = false
performanceWitnessCreatesSemanticIdentity = false
jsonSemanticCommandTransport = false
regexSemanticCommandParser = false
```

Anchor the owner to the existing `PortableSemanticInterpretationExact` abstraction rather than restating admission/reducer theory.

### Verify

```bash
agda -i . DASHI/Interop/PortableInteractiveGpuProjectionExact.agda
agda -i . DASHI/Interop/DioxusWgpuHyperfabricBridgeExact.agda
```

Do not broaden to the whole DASHI tree if unrelated old owners block it.

---

## Task 2 — Introduce a pure Rust Visualisation IR before any GPU code

### Files in `solfunmeme-dioxus`

Create:
- `src/visual/mod.rs`
- `src/visual/ir.rs`
- `src/visual/command.rs`
- `src/visual/selection.rs`

Update:
- `src/lib.rs`

### RED tests first

Create unit tests proving:

1. Dioxus/shell selection of object `42` and GPU-pick selection of object `42` decode to the same `DomainCommand::SelectObject(42)`.
2. Applying either decoded command to identical `SelectionState` produces identical next state.
3. A visual projection may omit a semantic object without deleting it from the semantic registry fixture.
4. A graph node and a chart datum may share the same `VisualObjectId` without becoming the same geometry primitive.
5. No semantic command codec requires JSON or regex.

### Minimal types

Prefer compact typed/in-memory Rust values:

```rust
VisualObjectId(u64)
SemanticRef(...stable typed ref...)
DomainCommand::SelectObject(VisualObjectId)
SelectionState { selected: Option<VisualObjectId> }
```

Visual IR:

```rust
Visualisation::Chart(ChartIr)
Visualisation::Timeline(TimelineIr)
Visualisation::Graph(GraphIr)
Visualisation::Sankey(SankeyIr)
Visualisation::Spatial(SpatialIr)
Visualisation::ProofTopology(ProofTopologyIr)
```

Only `ChartIr` and `GraphIr` need executable v0 geometry. The remaining variants may be typed placeholders **only if** they do not create fake implementation claims.

`GraphIr` v0:
- 3–5 stable-ID nodes;
- 2–4 weighted edges;
- deterministic positions supplied by fixture/projection, not a new layout engine.

`ChartIr` v0:
- a tiny set of stable-ID points/bars sharing the same selection identity namespace.

### Verify

```bash
cargo test visual
cargo check
```

---

## Task 3 — Add the wgpu engine behind a feature-compatible boundary

### Files

Update:
- `Cargo.toml`

Create:
- `src/visual/gpu/mod.rs`
- `src/visual/gpu/engine.rs`
- `src/visual/gpu/chart.rs`
- `src/visual/gpu/graph.rs`
- `src/visual/gpu/picking.rs`
- `src/visual/gpu/shaders/chart.wgsl`
- `src/visual/gpu/shaders/graph.wgsl`

### Dependency rule

Pin a `wgpu` version compatible with the repository's Rust/Dioxus toolchain after checking the current lock/toolchain. Add only the minimum helper crates needed for POD GPU buffers (for example `bytemuck` if required). Do not add a second charting framework.

### RED tests first

Keep semantic/geometry tests GPU-independent where possible:

- IR -> deterministic vertex/index instance data;
- stable object ID -> pick ID mapping;
- edge weight -> deterministic width/radius input;
- pick ID decode -> `GpuPickInput` -> `DomainCommand`.

Do **not** make headless adapter availability a unit-test prerequisite.

### Minimal renderer

Implement:

- one 2D chart pipeline;
- one graph pipeline with nodes + weighted edges;
- shared camera/viewport constants only as needed;
- integer/object-ID picking path;
- deterministic v0 coordinates;
- no force layout, no production Sankey ribbons, no LOD system yet.

The renderer consumes `Visualisation`/typed sub-IR. It must not inspect Dioxus component state to reconstruct topology.

---

## Task 4 — Host the visual surface in Dioxus without moving authority into Dioxus

### Files

Inspect current router/app structure first, then add the smallest compatible component, likely under:
- `src/components/visual_surface.rs` or repository-native equivalent;
- a small route/page such as `src/views/hyperfabric_v0.rs` only if the router pattern requires it.

Update:
- `src/app.rs` minimally.

### RED tests first

Where practical, test the pure event adapter rather than DOM rendering:

- Dioxus-side `Select` event for ID 42 decodes to `DomainCommand::SelectObject(42)`;
- GPU pick of ID 42 decodes identically;
- both flow through the same `reduce_selection` function.

### UI slice

Display:
- ordinary Dioxus controls/search/status/provenance text;
- one wgpu-owned canvas/surface;
- one Dioxus button/list item selecting an object;
- GPU picking selecting the same object;
- selected-object textual detail outside the GPU surface.

The Dioxus tree may display labels and details but must not be the source from which graph topology is reconstructed.

---

## Task 5 — Add the bounded Mabo visual specimen as a projection fixture

### Rule

This is a **visual/projection specimen**, not a new legal semantics implementation and not a claim that the UI proves Mabo.

### Files

Create a fixture/adapter in `solfunmeme-dioxus`, e.g.:
- `src/visual/fixtures/mabo_v0.rs`

Do not hard-code legal semantics inside GPU modules.

### Fixture shape

Use 3–5 semantic nodes corresponding to the already-approved bounded explanatory cone, approximately:

```text
prior proposition
-> challenged premise
-> Mabo proposition
-> immediate legal consequence
-> qualification/downstream application
```

Each visual node carries only stable semantic/source references required by the UI projection. Provenance/source inspection remains progressive/on-demand.

The default view should be readable and sparse. The graph is exposed when the user asks `Why?` / expands the proof cone, not dumped at startup.

### Reading/constituent compatibility

Retain the reading-trail principle that constituent and composite targets can overlap and remain independent (e.g. `silk`, `golden spider`, `golden spider silk`; `title`, `native title`). The renderer only needs stable IDs; it must not force one tokenisation.

### Tests

- fixture has bounded node/edge count;
- all IDs are stable/unique;
- selecting the Mabo proposition by Dioxus control and GPU pick produces identical selection state;
- source/context reference fields survive projection;
- hiding contextual nodes from default view does not remove them from the fixture/world registry.

---

## Task 6 — Native + browser portability compile gates

### Native

Confirm the shared Rust visual engine builds for the desktop target through repository-native Dioxus features.

### Browser

Confirm the same visual IR + wgpu/WGSL code builds for WASM/WebGPU. Platform-specific surface/bootstrap code may differ; semantic command decoding and visual IDs must not.

### Verification commands

Use commands compatible with the existing feature matrix discovered in `Cargo.toml`, approximately:

```bash
cargo test
cargo check --features desktop
cargo check --features web --target wasm32-unknown-unknown
```

If the WASM target/Dioxus CLI is absent locally, record that as an execution dependency rather than weakening parity claims.

Do not require identical pixels, timing, swapchain behavior, or GPU backend.

---

## Task 7 — Documentation and parity receipts

Create/update a short implementation note in `solfunmeme-dioxus` documenting:

```text
canonical semantics
-> Visualisation IR
-> wgpu renderer
-> pick/input proposal
-> shared admission/command reducer
```

Explicitly document:

- Dioxus owns ordinary shell UI;
- wgpu owns visual language;
- semantic identity is stable across both;
- rendering/performance differences do not change semantic identity;
- later eRDFa/IPFS/ZOS/zkperf/zkSEC integration is orthogonal and deferred.

Update the DASHI parity owner only for actual implemented ABI facts. Do not encode aspirational Sankey/layout behavior as paid.

---

## Deferred until v0 is GREEN

- production 3D Sankey layout/routing;
- GPU compute layout;
- edge bundling;
- labels at scale;
- LOD/culling;
- animation architecture beyond minimum selection feedback;
- federated graph streaming into GPU buffers;
- eRDFa/DA51 publication;
- DASL canonical-byte proofs;
- mesh/ZOS live sync;
- zkperf benchmarking;
- zkSEC remote authority/admission;
- broad legal/case UI.

## Completion criterion for this tranche

This tranche is complete only when fresh receipts demonstrate:

1. both focused Agda owners type-check;
2. pure Rust visual/command tests pass;
3. native Dioxus + wgpu build succeeds;
4. web/WASM build succeeds or is explicitly blocked only by missing local target/toolchain;
5. a Dioxus control and GPU pick for the same semantic object decode to the same command and selection state;
6. the bounded Mabo specimen renders through the framework-neutral IR without making Dioxus or wgpu semantic authority.

The next tranche after this should be chosen from observed bottlenecks, not pre-committed: either production Sankey/layout, Mabo source/proof-cone read-model wiring, or visual performance/LOD.