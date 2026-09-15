# Dioxus Shell + Independent wgpu Hyperfabric Design

## Status

Approved architectural direction for a Rust-first application shell and a first-class GPU graph interpreter.

The concrete application witness is `meta-introspector/solfunmeme-dioxus`, which already uses Dioxus 0.7.3, Dioxus web, WASM/browser bindings, `rsx!`, `Router`, `use_signal`, and `dioxus-charts`. The target architecture preserves that application investment while preventing Dioxus component state or chart widgets from becoming authoritative for the complex 3D graph surface.

This design extends the existing `PortableSemanticInterpretationExact` parent rather than replacing it.

## Core decision

Use:

```text
Dioxus shell + portable semantic state + independent wgpu graph interpreter
```

not:

```text
Dioxus -> dioxus-charts -> every visualization
```

and not:

```text
pure wgpu app with the existing Dioxus application discarded
```

The Dioxus shell owns normal application UI: routing, forms, search, document panes, tables, provenance cards, settings, accessible controls, and ordinary analytical charts.

The wgpu lane owns complex visual computation and rendering: 3D Sankey/hyperfabric geometry, GPU buffers, picking, camera state, LOD/culling, graph-layout compute, edge bundling, flow animation, and WGSL pipelines.

## Semantic application

Let

```text
A = (S, C, delta)
```

where:

- `S` is semantic/domain state;
- `C` is the domain-command language;
- `delta : S x C -> S` is the semantic transition.

Neither Dioxus events nor GPU input events are themselves the command language.

The important separation is:

```text
native input event != domain command != semantic transition
```

## Independent projections

Define two sibling projections from semantic state:

```text
pi_D : S -> D
pi_G : S -> G
```

`D` is the ordinary Dioxus/application view model. Typical fields include routes, forms, search state, selected semantic target, inspector/provenance panels, textual reading state, and ordinary chart data.

`G` is the graph/GPU view model. A minimal graph projection is:

```text
G = (V, E, P, F, L)
```

where:

- `V` = nodes;
- `E` = edges/hyperedges;
- `P` = positions/layout state;
- `F` = flow/weight data;
- `L` = visual-layer, LOD, selection, and picking metadata.

The architectural non-factorisation rule is:

```text
pi_G need not FactorsThrough(pi_D)
pi_D need not FactorsThrough(pi_G)
```

A Dioxus component tree is therefore not the canonical source of graph topology or GPU resources.

## Framework-neutral graph IR

The graph IR must be independent of Dioxus and wgpu resource handles.

Conceptually:

```text
Node = (
  id,
  position,
  extent,
  semanticRef,
  flags
)

Edge = (
  id,
  src,
  dst,
  flow,
  bundle,
  provenanceRef,
  flags
)
```

The semantic graph contract concerns endpoint identity, graph relations, flow/weight meaning, provenance references, and consumer-required selection semantics.

It does not require equal triangles, equal shader invocations, equal rasterization, equal execution order, or equal performance across backends.

For a 3D Sankey edge `e`, an implementation may derive geometry such as:

```text
Gamma(e) = Sweep(Curve(p_src, ..., p_dst), width(flow(e)))
```

but `Gamma` is an interpreter-level realization, not the semantic identity of `e`.

## GPU interpreter

The graph renderer is a sibling consumer of graph IR and owns long-lived GPU resources such as:

```text
GraphGpu
  node_buffer
  edge_buffer
  flow_buffer
  camera
  picking_buffer
  layout_compute
  render_pipeline
  shaders
```

Web deployment:

```text
Rust/WASM -> wgpu -> browser WebGPU
```

Native deployment:

```text
Rust -> wgpu -> native backend
```

The same semantic graph and Rust graph engine may be shared even where execution strategy, supported limits, timing, and raster output differ.

## Dioxus interpreter

Dioxus remains the application shell and ordinary-UI interpreter.

A graph-hosting Dioxus component is only a controller/host. It may expose filters, routing, selection summaries, provenance, and graph-surface placement, but it does not own GPU topology or buffers.

The graph surface must remain removable/rehostable without rewriting semantic state or graph IR.

`dioxus-charts` remains appropriate for conventional bar/line/pie-style analytical views. It is not the architectural owner for the 3D Sankey/hyperfabric surface.

## Interaction refinement

Dioxus and GPU interactions may be different mechanisms that refine to the same command.

Example:

```text
Dioxus side-panel click
  -> decode_D
  -> SelectNode(42)

GPU ray/pick hit
  -> decode_G
  -> SelectNode(42)
```

The semantic invariant is:

```text
decode_D(i_D) = decode_G(i_G) = SelectNode(42)
```

for interactions that denote the same consumer-relevant selection.

Then:

```text
delta(S, SelectNode(42))
```

is independent of which interpreter emitted the command.

The same pattern applies to `FollowTarget(id)` from the semantic-reading work: DOM activation, Dioxus component activation, or GPU picking may all emit the same domain command after boundary admission.

## Portable semantic refinement

This architecture is an instance of `PortableSemanticInterpretationExact`.

For an intent/IR object `x`, a backend `b`, and consumer observation `Q`:

```text
Q(interpret_b(x)) = Q(meaning(x))
```

is the required semantic-refinement receipt.

For GPU rendering, `Q` should normally observe graph semantics such as selected object identity, endpoint connectivity, flow quantity, visibility class, or interaction result—not raw framebuffer identity.

Consequently:

```text
same semantics != same syntax
same semantics != same algorithm
same semantics != same execution order
same semantics != same geometry
same semantics != same pixels
same semantics != same performance
```

## Cross-repository role map

### `meta-introspector/solfunmeme-dioxus`

Concrete Dioxus/WASM shell witness.

Role:

```text
application chrome + routes + ordinary controls + ordinary charts
```

Not authority for graph semantics or GPU realization.

### `meta-introspector/erdfa-publish-rs`

Existing semantic-presentation IR precedent. It defines typed Rust components serialized as content-addressed DA51 CBOR shards and explicitly separates semantic component structure from renderer choice.

This should be reused conceptually for graph/provenance shard representation rather than inventing a second generic presentation ontology.

Potential graph relation:

```text
semantic graph object
  -> content-addressed shard / manifest
  -> renderer-specific realization
```

The CFT multi-scale decomposition also provides a precedent for multiple simultaneously valid semantic scales rather than one forced display granularity.

### `meta-introspector/ipfs-dasl`

Canonical serialization/conformance witness.

Role:

```text
same input bytes
  -> multiple implementation adapters
  -> accept/reject comparison
  -> canonical-byte equality / idempotence checks
```

This is a concrete instance of semantic interpretation plus stricter serialization queries. The GPU architecture should reuse the distinction:

```text
semantic-equivalent rendering
```

does not automatically imply:

```text
canonical-byte-equal serialization
```

unless the consumer explicitly asks for the latter.

### `meta-introspector/mesh-sync-rs`

Transport/synchronization witness. It discovers peers, pulls and pushes structured logs, and keeps transport failure local to a peer operation.

Role:

```text
replication transport != semantic authority
```

Graph updates received through a mesh transport remain candidate state until admitted by the semantic/application boundary.

### `meta-introspector/zos-server`

Distributed reconciliation/runtime witness. Its documented sync lane distinguishes inventory/reconciliation/replay/transport from canonical identity and explicitly avoids turning the synchronization layer into a receipt/timeline ledger.

Role:

```text
transport/recovery capability != canonical graph identity
```

Its zkperf/eRDFa-shaped identity normalization is a useful upstream adapter precedent.

### `chboishabba/zkperf`

Observation/performance receipt witness.

Role:

```text
execution strategy
  -> measured witness / trace / performance receipt
```

This is downstream operational evidence, not semantic identity. It can compare JS/Rust/WASM/WebGPU/native strategies without changing the graph meaning.

### `chboishabba/zkSEC`

Authority/admission firewall witness. Its architecture explicitly treats public/uncertain signals as proposal-only and requires verified actor, authorized scope, and explicit receipt flow for high-authority mutation.

Role:

```text
candidate input / transport / UI event
  -> admission gate
  -> authorized semantic mutation
```

This is the correct place to cross-pollinate `Fails(here) != Fails(everywhere)` and `input event != mutation authority`.

### `meta-introspector/kant-zk-pastebin`

Persistence/publication witness. It already depends on `erdfa-publish`, CBOR/IPLD/unixfs/IPFS-related crates, and HTTP/server surfaces.

Role:

```text
semantic/provenance shard publication and retrieval
```

It should remain a persistence/distribution adapter rather than becoming the canonical graph store by implication.

## Shard / graph / rendering relationship

A useful composition is:

```text
Semantic state S
  -> graph projection G
  -> content-addressed semantic shards H
  -> graph renderer R
```

where both `G` and `H` retain semantic/provenance identity, while `R` owns transient GPU realization.

GPU handles, buffers, pipelines, bind groups, textures, and triangles are therefore execution resources, not durable semantic identifiers.

## Admission and failure locality

Any external graph update, JSON command, mesh event, persisted shard, or UI/GPU event must enter through an explicit admission boundary before obtaining semantic mutation authority.

Conceptually:

```text
Input
  -> decode
  -> validate
  -> Admissible?
  -> DomainCommand
  -> delta
```

Failure at one boundary does not imply application-wide failure:

```text
Fails(here) != Fails(everywhere)
```

Malformed transport payloads, unknown graph ids, stale CIDs, unsupported GPU capabilities, or invalid commands must remain local failures unless a higher-level consumer explicitly escalates them.

## Formal owner decomposition

The generic parent remains:

```text
PortableSemanticInterpretationExact
```

Add a child owner along the lines of:

```text
PortableInteractiveGpuProjectionExact
```

with conceptual fields:

```text
SemanticState
DomainCommand
step

DioxusView
projectDioxus

GraphView
projectGraph

DioxusInput
GpuInput

decodeDioxus
decodeGpu

GraphSemanticQuery
GpuImplementation
GpuObservation
semanticRefinement
```

A separate concrete bridge should instantiate the architecture for the Dioxus/wgpu application witness rather than putting Dioxus names in the generic core.

Suggested concrete bridge:

```text
DioxusWgpuHyperfabricBridgeExact
```

## First concrete implementation slice

After spec approval, the smallest retained implementation should be a tiny graph specimen with:

- 3-5 semantic nodes;
- 2-4 weighted edges;
- one overlapping provenance/reference relation;
- Dioxus-hosted graph surface;
- wgpu/WGSL rendering of the graph surface;
- GPU picking that emits an ordinary domain `SelectNode` command;
- Dioxus side-panel activation that emits the same command;
- tests proving command-level equivalence without asserting equal pixels or equal event mechanisms.

The first slice does not need production 3D Sankey layout. A minimal rendered graph is sufficient to prove the architecture before adding layout compute, ribbon extrusion, LOD, or bundling.

## Firewalls

```text
Dioxus component state != domain authority
Dioxus renderer != graph renderer
dioxus-charts != 3D graph engine
semantic graph != GPU buffers
semantic graph != triangles
same semantic graph != same GPU geometry
same semantic graph != same pixels
same command != same input mechanism
mesh transport != mutation authority
content address != legal/domain authority
performance witness != semantic identity
security proposal != authorized action
hidden from renderer != absent from semantic world
```

## Success criteria

The architecture is successful when:

1. the Dioxus shell can be replaced or bypassed without changing semantic graph identity;
2. the wgpu renderer can be hosted by web/WASM or native execution without changing domain-command semantics;
3. ordinary charts can continue using `dioxus-charts` independently of the 3D graph engine;
4. graph/provenance objects can be serialized/content-addressed without GPU handles becoming durable identity;
5. transport/persistence/security/performance systems remain distinct downstream/upstream roles;
6. Dioxus and GPU interactions can refine to the same domain command;
7. consumer-indexed semantic equivalence is required instead of pixel/geometry/execution equivalence.
