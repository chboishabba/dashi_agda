# DASHI repository-history visualizer

This package is the concrete Python/Manim realization of:

- `DASHI.Core.TemporalSemanticGraphExact`
- `DASHI.Core.VersionedStateGraphExact`
- `DASHI.Visual.RepositoryEvolutionEverything`

The formal layer owns the semantic contract. Python owns extraction and rendering only.

## Architecture

```text
Git DAG / future Casey provider
            |
            v
     VersionedStateGraph
            |
      materialization
            |
            v
      Agda source tree
            |
     tree-sitter-agda
            |
            v
       SemanticGraph
            |
         GraphDelta
            |
            v
      Manim DiGraph
```

No dependency edge is hand-authored. The Agda frontend:

1. parses each `.agda` blob with `tree-sitter/tree-sitter-agda`,
2. captures declaration names, binders, and identifier references,
3. assigns references to the smallest enclosing declaration,
4. removes local binders and self references,
5. resolves same-module and qualified names directly, then admits unqualified cross-module names only through actual `open`/`open import` scope evidence,
6. respects `using`, `hiding`, and `renaming`, and leaves all remaining ambiguity unresolved rather than manufacturing an edge.

Git branch/merge topology is likewise extracted from commit parents. A commit
with two or more parents is a merge node. A parent with multiple children
produces a visible lane split in the deterministic history layout.

## Parser choice

The canonical grammar is `https://github.com/tree-sitter/tree-sitter-agda`.
The package pins `tree-sitter-agda==1.3.3`; that release declares
`tree-sitter~=0.22`, so the adapter deliberately accepts the 0.22 parser/query
API shape instead of depending on a newer incompatible binding.

## Install

From this directory:

```bash
python -m pip install -e .
```

## Extract

Fast branch/merge topology only:

```bash
dashi-repo-history extract ../../.. --history-only --max-commits 300 -o /tmp/dashi-history.json
```

Earliest history (useful for the origin movie):

```bash
dashi-repo-history extract ../../.. --history-only --first-commits 150 -o /tmp/dashi-early-history.json
```

Full semantic extraction is deliberately bounded first because the graph is large:

```bash
dashi-repo-history extract ../../.. --max-commits 100 -o /tmp/dashi-semantic-history.json
```

A more legible first semantic film:

```bash
dashi-repo-history extract ../../.. \
  --path-prefix DASHI/Arithmetic/ \
  --max-commits 60 \
  -o /tmp/dashi-arithmetic-history.json
```

## Render branch/merge history

```bash
dashi-repo-history render /tmp/dashi-history.json --quality -qm
```

## Render one semantic symbol graph

```bash
dashi-repo-history render /tmp/dashi-arithmetic-history.json \
  --scene snapshot --snapshot-index -1 --quality -qm
```

## Formal/implementation boundary

- Git or another version-state producer owns commit/candidate/workspace history.
- Tree-sitter owns syntactic observation; the resolver owns dependency admission.
- The semantic graph owns symbol identity and graph deltas.
- Manim owns only layout, camera movement, and animation realization.
- Ambiguous references remain explicit unresolved observations.

## Implemented evolution semantics

The current pipeline already includes:

- parent-relative semantic deltas for every commit parent,
- persistent mental-map layout across semantic snapshots,
- unique structural-fingerprint continuity across supported moves/renames,
- clause-scoped binders and constructor-pattern relations,
- explicit fork-to-merge branch episodes,
- renderer-neutral scene programs,
- focused merge attribution,
- simple-visual-graph projection without loss of semantic authority.

Remaining larger extensions are Casey candidate/workspace/build materializations,
cross-repository semantic edges, and richer expression/application subgraphs.

## Semantic evolution scene

The continuous semantic movie follows a real first-parent lineage; it never
uses arbitrary topological neighbours as if they were parent/child states.

```bash
dashi-repo-history render /tmp/dashi-arithmetic-history.json \
  --scene semantic-history \
  --quality -qm
```

Choose a different lineage head explicitly:

```bash
dashi-repo-history render /tmp/dashi-arithmetic-history.json \
  --scene semantic-history \
  --target-commit <sha> \
  --quality -qm
```

## Full fork → branches → merge scene

For this scene, extract semantic history with episode closure enabled so sampled
history cannot hide the real fork or intermediate branch commits:

```bash
dashi-repo-history extract ../../.. \
  --path-prefix DASHI/Arithmetic/ \
  --max-commits 120 \
  --episode-context \
  -o /tmp/dashi-arithmetic-episodes.json
```

Inspect the recovered episodes first:

```bash
dashi-repo-history episodes /tmp/dashi-arithmetic-episodes.json
```

Then render one episode:

```bash
dashi-repo-history render /tmp/dashi-arithmetic-episodes.json \
  --scene episode \
  --episode-index 0 \
  --quality -qm
```

The episode scene starts from the actual fork semantic graph, splits it into two
live graph views, advances each side along its parent-evidenced branch path in
repository order, then converges to the merge graph and highlights merge-only
symbols.

## Merge convergence scene

Merge contribution is derived from both actual parent semantic snapshots.
The focused scene restricts the display to the changed subgraph and separates
common, parent-only, removed, and merge-only nodes/relations.

```bash
dashi-repo-history render /tmp/dashi-arithmetic-history.json \
  --scene merge \
  --episode-index 0 \
  --quality -qm
```

Manim `DiGraph` geometrically projects parallel typed relations sharing the
same source/target pair to one visual edge. The JSON retains every typed
`relation_id`; `DASHI.Visual.SemanticGraphProjectionExact` formalizes that
this display quotient never becomes the semantic authority graph.

## Rewritten-history archaeology

`git rev-list --all` cannot recover commits made unreachable by a rewritten
history. Recovered commit ids can therefore be supplied as traversal seeds:

```bash
dashi-repo-history extract ../../.. \
  --seed-commit 9955429d8dbe1aae4bbf3778808993cfdc6172c9 \
  --fetch-seeds \
  --first-commits 150 \
  -o /tmp/dashi-archaeology.json
```

The seed is data supplied by the operator; no historical SHA is hard-coded
into the extraction engine.

## Language adapters

`HistoryExtractor` depends on the `LanguageAdapter` protocol rather than Agda
directly. The current `AgdaLanguageAdapter` supplies `.agda` suffixes,
Tree-sitter file extraction, and semantic graph assembly. Future Lean/Rust/
Python frontends can provide the same three operations with their own query
resources while reusing Git history, identity, layout, merge attribution, and
Manim scenes unchanged.

## Identity across refactors

Top-level declarations carry a structural fingerprint with their own spelling
masked. Exact semantic ids remain authoritative. A unique kind+fingerprint
match can guide visual continuity for a file move or rename; repeated/
ambiguous fingerprints are left unmatched rather than guessed.

## Rooted symbol construction zoom

List stable semantic selectors in a snapshot:

```bash
dashi-repo-history symbols /tmp/dashi-arithmetic-history.json \
  --query CancellationPressure
```

Render one declaration and automatically unfold its semantic neighborhood:

```bash
dashi-repo-history render /tmp/dashi-arithmetic-history.json \
  --scene symbol \
  --symbol DASHI.Arithmetic.CancellationPressureCore::someDeclaration \
  --upstream-depth 3 \
  --downstream-depth 1 \
  --quality -qm
```

The symbol selector may be a full semantic id, a unique bare label, or
`Module.Name::label`. The scene reveals the root first, then increasingly
distant dependencies and finally downstream consumers. All links come from
the extracted semantic graph; focus traversal cannot invent dependencies.

## Follow one construction through history

Once a target symbol exists at the lineage head, the temporal focus scene
walks backward through real first-parent snapshots using exact semantic IDs or
uniquely supported refactor evidence, stops at the symbol's introduction (or
earliest safely matched state), then animates the focused neighborhood forward:

```bash
dashi-repo-history render /tmp/dashi-arithmetic-history.json \
  --scene symbol-history \
  --symbol DASHI.Arithmetic.CancellationPressureCore::someDeclaration \
  --upstream-depth 3 \
  --downstream-depth 1 \
  --quality -qm
```

To follow a historical symbol that no longer exists at the newest snapshot,
select a lineage head where it still exists:

```bash
dashi-repo-history render /tmp/dashi-history.json \
  --scene symbol-history \
  --target-commit <sha> \
  --symbol Module.Name::symbol \
  --quality -qm
```

Exact semantic identity is preferred. A rename or move is followed only when
the existing identity layer has unique supported evidence; ambiguous
similarity terminates the historical focus rather than guessing continuity.

## Export the renderer-neutral scene program

The same orchestration consumed by Manim can be serialized independently:

```bash
dashi-repo-history program /tmp/dashi-arithmetic-history.json \
  --scene symbol-history \
  --symbol DASHI.Arithmetic.CancellationPressureCore::someDeclaration \
  --upstream-depth 3 \
  --downstream-depth 1 \
  -o /tmp/cancellation-pressure-scene.json
```

The output schema is `dashi.scene-program.v1`. This is the intended handoff
surface for future SVG/WebGPU/ITIR renderers; those backends should interpret
the program rather than recomputing semantic history or dependency admission.


## Design archaeology: lessons from the June 2026 repository index

The earlier `scripts/repo_index.py` and `scripts/agda_import_cone.py` are useful
predecessors. The new visualizer intentionally keeps several good ideas:

- source remains the authority; an index/rendering layer does not promote truth,
- stable machine-readable symbol identities,
- explicit unresolved observations rather than silently fabricating certainty,
- incremental file/blob reuse,
- bounded human-facing query output,
- reverse/dependency traversal with visited-node tracking,
- durable structured output suitable for several frontends.

The old index also exposes scaling patterns that this implementation should not
repeat.

### 1. Do not generate global candidate references and prune them later

The old index tokenized identifier-looking strings across source/docs and then
linked mentions against symbols using several corpus-wide predicates. It needed
protective heuristics such as:

```text
MIN_BARE_NAME_LENGTH = 4
MAX_BARE_NAME_FANOUT = 8
```

That is evidence that bare-name candidate generation itself can become the
dominant problem.

The Tree-sitter frontend instead admits an unqualified dependency only from
lexical/module/open-scope evidence. A globally unique spelling is deliberately
not scope evidence.

### 2. Imports are module relations, not edges to every declaration

The old relinker included a join equivalent to:

```sql
JOIN symbols s ON s.module = imported_module
```

which can turn one module import into references to every symbol in the imported
module. The new graph keeps `imports` / `opens` as module relations and emits
declaration edges only when syntax plus scope resolution supports them.

### 3. Incremental parsing is not enough if linking is global

The old incremental updater reparsed changed files, but then
`_relink_all()` deleted/rebuilt the complete reference table. Therefore a
small source edit could still cause corpus-wide linking work.

The new architecture explicitly forbids "one changed file implies global
relink" as its default semantic contract. Blob parsing is cached already; the
next optimization surface is affected-scope invalidation rather than a global
relink phase.

### 4. Depth is not a resource bound

Both the old recursive graph query and import-cone traversal correctly used
visited-node sets, but a high-degree graph can still become enormous at shallow
depth. New rooted focus therefore has independent defaults:

```text
max focus nodes = 250
max focus edges = 800
```

and emits a truncation receipt. Depth describes semantic distance; the budgets
bound presentation work.

### 5. Do not run force layout on an unexpectedly large graph

Small semantic graphs still use a bounded spring refinement. Above 180 nodes or
600 projected edges, the renderer switches to deterministic large-graph
placement: retain existing positions, anchor new nodes near positioned semantic
neighbours, and grid-place unanchored components. Large graphs never enter the
iterative force solver.

### 6. Compute only the history actually being narrated

Whole-repository branch topology may use all refs. Semantic movies should
usually use an explicit lineage root:

```bash
dashi-repo-history extract ../../.. \
  --ref HEAD \
  --max-commits 80 \
  -o /tmp/dashi-head-semantic.json
```

This avoids mixing unrelated branch tips into a semantic evolution film merely
because they are recent in `git rev-list --all`.

### 7. Time is data, not frame number

The Git-history scene uses real commit timestamps on the vertical axis and
branch lanes horizontally. Large gaps in development therefore look large; a
burst of many commits in one day remains visually compressed in time. Semantic
single-graph scenes show the exact UTC commit date in their scene stamp instead
of overloading dependency geometry with a second Y-axis meaning.


## Python vs Rust backend decision

The current implementation deliberately keeps Python as the reference backend
until measured history runs justify moving the deterministic patch core.

This is not because implementation language is irrelevant. It is because the
largest avoidable costs discovered so far were architectural:

1. global candidate linking,
2. whole-corpus relinking after local edits,
3. unbounded traversal/layout,
4. full graph duplication at every commit,
5. repeated resolution-impact scans,
6. recomputing unchanged portions of affected modules.

Items 1-5 now have explicit mitigations in the current branch:

```text
scope-evidenced resolution
affected-module patches
hard focus/layout budgets
checkpoint + delta history
persistent resolution-impact index
```

Item 6 is measured explicitly as physical recomputation inflation.

A profiled extraction can be run with:

```bash
dashi-repo-history extract ../../.. \
  --ref HEAD \
  --max-commits 500 \
  --compact \
  --checkpoint-interval 50 \
  --parity-every 25 \
  --profile-output /tmp/dashi-profile.json \
  -o /tmp/dashi-history.json

dashi-repo-history profile /tmp/dashi-profile.json
```

The backend policy intentionally orders fixes as follows:

```text
not enough samples
    -> keep Python reference

affected-module fanout too high
    -> fix invalidation boundaries

impact planning dominates
    -> persistent resolution-impact index first

patching dominates but recomputation >> semantic change
    -> direct-delta affected-module patching first

patching still dominates after those fixes
    -> Rust semantic core candidate
```

The default Rust-candidate gate currently requires at least 50 incremental
samples, patch p95 above 50 ms, and patch work above 35% of measured incremental
wall time. These are configurable policy thresholds, not semantic constants.

### If Rust is admitted

The intended design follows the useful SensibLaw/SLR split rather than porting
the visualizer wholesale:

```text
Python
  Git traversal
  tree-sitter observation adapter
  scene-program orchestration
  Manim renderer
        |
        | changed/deleted observation stream
        v
long-lived Rust semantic workspace
  versioned parent states
  resolution-impact index
  deterministic semantic patch compiler
  patch/parity/performance receipts
        |
        v
Python scene/history layer
```

A Rust backend should **not** spawn once per commit and should **not** receive
the whole corpus on each update. It should retain versioned workspace state and
consume only changed/deleted observations, analogous to SLR's direct-delta
runtime.

Until the profile gate says otherwise, the recommended implementation remains
the Python affected-module backend because Tree-sitter parsing is already
native-backed, the graph sizes presented to Manim are bounded, history storage
is delta-native, and resolution impact is incrementally indexed.
