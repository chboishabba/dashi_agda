# Dioxus Shell + Independent wgpu Visualisation/Hyperfabric Design

## Status

Revised architectural direction for a Rust-first application shell and a first-class GPU visualisation interpreter.

The concrete application witness is `meta-introspector/solfunmeme-dioxus`, which already uses Dioxus 0.7.3, Dioxus web, WASM/browser bindings, `rsx!`, `Router`, `use_signal`, and `dioxus-charts`. The target architecture preserves that application investment while preventing Dioxus component state or chart widgets from becoming authoritative for any interactive visualisation surface.

This design extends the existing `PortableSemanticInterpretationExact` parent rather than replacing it.

## Core decision

Use:

```text
Dioxus ordinary-UI shell + portable semantic state + independent wgpu visualisation engine
```

not:

```text
Dioxus -> dioxus-charts -> visualisation
```

and not:

```text
pure wgpu app with the existing Dioxus application discarded
```

The Dioxus shell owns ordinary application UI:

- routing;
- menus and navigation;
- forms;
- search inputs;
- document/reading panes;
- settings;
- textual provenance and citation cards;
- ordinary non-visual data tables;
- accessibility/chrome around the visual surface;
- commands and selectors that configure a visualisation.

The wgpu lane owns **all charts and interaction-heavy visualisation**, including:

- bar, line, area, pie, scatter and other analytical charts;
- timelines and interval views;
- 2D graph views;
- 3D Sankey/hyperfabric geometry;
- proof/dependency topology;
- GPU buffers;
- picking and brushing;
- pan/zoom/orbit cameras;
- hover/selection overlays;
- LOD/culling;
- graph-layout compute;
- edge bundling;
- flow animation;
- spatial aggregation;
- WGSL render and compute pipelines.

`dioxus-charts` is therefore an existing implementation/prototype witness, not part of the durable target visualisation architecture.

The strong ownership rule is:

```text
Dioxus owns ordinary UI.
wgpu owns visualisation.
```

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

Define sibling projections from semantic state:

```text
pi_D : S -> D
pi_V : S -> V
```

`D` is the ordinary Dioxus/application view model. Typical fields include routes, forms, search state, selected semantic target, textual inspector/provenance state, document-reading state, configuration controls, and parameters which configure a visualisation.

`V` is the framework-neutral visualisation view model consumed by the GPU engine.

The architectural non-factorisation rule is:

```text
pi_V need not FactorsThrough(pi_D)
pi_D need not FactorsThrough(pi_V)
```

A Dioxus component tree is therefore not the canonical source of chart data, graph topology, geometric state, or GPU resources.

## Framework-neutral visualisation IR

The visualisation IR must be independent of both Dioxus and wgpu resource handles.

The IR may contain multiple consumer-specific visual families under one typed surface, for example:

```text
Visualisation
  = Chart(ChartIR)
  | Timeline(TimelineIR)
  | Graph(GraphIR)
  | Sankey(SankeyIR)
  | Spatial(SpatialIR)
  | ProofTopology(ProofTopologyIR)
```

This does not require every family to share one geometry representation. They share the semantic/interpreter boundary, interaction command surface, provenance references, and execution ownership.

A chart IR may be conceptually:

```text
ChartIR = (
  chartId,
  series,
  axes,
  marks,
  scales,
  semanticRefs,
  interactionPolicy
)
```

A graph IR may be conceptually:

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

The semantic contract concerns data identity, graph relations, flow/weight meaning, series/axis meaning, provenance references, and consumer-required interaction semantics.

It does not require equal triangles, equal shader invocations, equal rasterization, equal execution order, or equal performance across backends.

For a 3D Sankey edge `e`, an implementation may derive geometry such as:

```text
Gamma(e) = Sweep(Curve(p_src, ..., p_dst), width(flow(e)))
```

but `Gamma` is an interpreter-level realization, not the semantic identity of `e`.

Likewise a line chart series may become a GPU polyline, a triangle strip, or another batched geometry without changing the series semantics.

## GPU visualisation interpreter

The renderer is a sibling consumer of visualisation IR and owns long-lived GPU resources such as:

```text
VisualGpu
  mark_buffers
  node_buffer
  edge_buffer
  flow_buffer
  axis_buffers
  camera
  picking_buffer
  selection_buffer
  layout_compute
  render_pipelines
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

The same semantic visualisation IR and Rust renderer may be shared even where execution strategy, supported limits, timing, and raster output differ.

## Dioxus interpreter

Dioxus remains the application shell and ordinary-UI interpreter.

A visualisation-hosting Dioxus component is only a controller/host. It may expose filters, routing, search, selection summaries, provenance, textual details, settings, and visual-surface placement, but it does not own visual geometry, chart marks, graph topology, layout buffers, or GPU state.

The visual surface must remain removable/rehostable without rewriting semantic state or visualisation IR.

Existing `dioxus-charts` use is treated as historical/prototype implementation evidence. Durable analytical charts migrate to the same wgpu visualisation engine used for Sankey, hyperfabric, graph and proof-topology surfaces.

## One visualisation engine, multiple semantic views

The reason for putting ordinary charts into wgpu as well is architectural coherence rather than GPU novelty.

A scatter plot, line chart, timeline, dependency graph and Sankey all need overlapping capabilities:

```text
semantic object identity
projection/scales/layout
GPU-resident geometry
selection
hover
picking
brushing
filtering
zoom/camera
provenance overlays
animation
LOD
```

Keeping these in one engine allows one interaction and rendering substrate instead of separate DOM/SVG/chart-library and GPU worlds.

This does **not** mean every simple chart must use expensive 3D machinery. The same GPU engine may have lightweight 2D pipelines and richer 3D pipelines.

Conceptually:

```text
VisualGpu
  2d/
    bars
    lines
    points
    areas
    timelines
  graph/
    nodes
    edges
    labels
  sankey3d/
    ribbons
    bundles
    flow
  interaction/
    picking
    brushing
    selection
```

## Interaction refinement

Dioxus and GPU interactions may be different mechanisms that refine to the same command.

Example:

```text
Dioxus side-panel click
  -> decode_D
  -> SelectNode(42)

GPU pick hit
  -> decode_V
  -> SelectNode(42)
```

The semantic invariant is:

```text
decode_D(i_D) = decode_V(i_V) = SelectNode(42)
```

for interactions that denote the same consumer-relevant selection.

Then:

```text
delta(S, SelectNode(42))
```

is independent of which interpreter emitted the command.

Likewise a GPU bar click, timeline selection, graph-node pick, Sankey-ribbon pick, or proof-node pick may all emit ordinary domain commands such as:

```text
SelectObject(id)
FollowTarget(id)
FilterBy(predicate)
SetRange(a, b)
FocusProvenance(id)
```

The same pattern applies to the semantic-reading work: Dioxus text activation or GPU picking may emit the same domain command after boundary admission.

## Portable semantic refinement

This architecture is an instance of `PortableSemanticInterpretationExact`.

For an intent/IR object `x`, a backend `b`, and consumer observation `Q`:

```text
Q(interpret_b(x)) = Q(meaning(x))
```

is the required semantic-refinement receipt.

For GPU visualisation, `Q` should normally observe semantics such as selected object identity, series identity, endpoint connectivity, flow quantity, range/filter result, visibility class, or interaction result—not raw framebuffer identity.

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

Target role:

```text
application chrome + routes + ordinary controls + textual/document UI
```

Existing `dioxus-charts` is not the target owner of analytical visualisation.

### `meta-introspector/erdfa-publish-rs`

Existing semantic-presentation IR precedent. It defines typed Rust components serialized as content-addressed DA51 CBOR shards and explicitly separates semantic component structure from renderer choice.

This should be reused conceptually for visual/provenance shard representation rather than inventing a second generic presentation ontology.

Potential relation:

```text
semantic visual object
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

Visualisation updates received through a mesh transport remain candidate state until admitted by the semantic/application boundary.

### `meta-introspector/zos-server`

Distributed reconciliation/runtime witness. Its documented sync lane distinguishes inventory/reconciliation/replay/transport from canonical identity and explicitly avoids turning the synchronization layer into a receipt/timeline ledger.

Role:

```text
transport/recovery capability != canonical visual/domain identity
```

Its zkperf/eRDFa-shaped identity normalization is a useful upstream adapter precedent.

### `chboishabba/zkperf`

Observation/performance receipt witness.

Role:

```text
execution strategy
  -> measured witness / trace / performance receipt
```

This is downstream operational evidence, not semantic identity. It can compare JS/Rust/WASM/WebGPU/native strategies without changing the visualisation meaning.

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

It should remain a persistence/distribution adapter rather than becoming the canonical visual/domain store by implication.

## Shard / visualisation / rendering relationship

A useful composition is:

```text
Semantic state S
  -> visualisation projection V
  -> content-addressed semantic shards H
  -> GPU renderer R
```

where both `V` and `H` retain semantic/provenance identity, while `R` owns transient GPU realization.

GPU handles, buffers, pipelines, bind groups, textures, marks and triangles are therefore execution resources, not durable semantic identifiers.

## Admission and failure locality

Any external visual update, JSON command, mesh event, persisted shard, or Dioxus/GPU event must enter through an explicit admission boundary before obtaining semantic mutation authority.

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

Malformed transport payloads, unknown semantic ids, stale CIDs, unsupported GPU capabilities, or invalid commands must remain local failures unless a higher-level consumer explicitly escalates them.

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

VisualView
projectVisual

DioxusInput
GpuInput

decodeDioxus
decodeGpu

VisualSemanticQuery
GpuImplementation
GpuObservation
semanticRefinement
```

A separate concrete bridge should instantiate the architecture for the Dioxus/wgpu application witness rather than putting Dioxus names in the generic core.

Suggested concrete bridge:

```text
DioxusWgpuHyperfabricBridgeExact
```

The generic core should talk about visualisation rather than Sankey specifically so line/scatter/bar/timeline/graph views instantiate the same owner.

## First concrete implementation slice

After spec approval, the smallest retained implementation should prove both sides of the new ownership rule:

- a Dioxus ordinary-UI host/control surface;
- a wgpu-hosted visual surface;
- one tiny 2D interactive chart specimen using GPU marks;
- one tiny weighted graph/Sankey specimen;
- shared semantic object ids between visual forms;
- GPU picking that emits an ordinary domain command;
- a Dioxus control that emits the same command;
- tests proving command-level equivalence without asserting equal pixels or equal event mechanisms.

The first slice does not need production 3D Sankey layout. Minimal GPU chart marks plus a minimal rendered graph are sufficient to prove that charts and graph visualisations share the wgpu-owned visual lane before adding layout compute, ribbon extrusion, LOD, or bundling.

## Firewalls

```text
Dioxus component state != domain authority
Dioxus renderer != visualisation renderer
dioxus-charts != durable chart architecture
semantic chart != GPU mark buffers
semantic graph != GPU buffers
semantic graph != triangles
same semantic visualisation != same GPU geometry
same semantic visualisation != same pixels
same command != same input mechanism
mesh transport != mutation authority
content address != legal/domain authority
performance witness != semantic identity
security proposal != authorized action
hidden from renderer != absent from semantic world
```

## Success criteria

The architecture is successful when:

1. the Dioxus shell can be replaced or bypassed without changing semantic visualisation identity;
2. the wgpu renderer can be hosted by web/WASM or native execution without changing domain-command semantics;
3. **all retained charts and interactive visualisations use the wgpu visualisation engine rather than a Dioxus chart renderer**;
4. lightweight 2D charts and complex 3D Sankey/hyperfabric views can share interaction, picking, selection and provenance infrastructure while retaining distinct pipelines;
5. visual/provenance objects can be serialized/content-addressed without GPU handles becoming durable identity;
6. transport/persistence/security/performance systems remain distinct downstream/upstream roles;
7. Dioxus and GPU interactions can refine to the same domain command;
8. consumer-indexed semantic equivalence is required instead of pixel/geometry/execution equivalence.
