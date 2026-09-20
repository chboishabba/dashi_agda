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
5. resolves same-module, qualified, then globally-unique symbols,
6. leaves ambiguity unresolved rather than manufacturing an edge.

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
dashi-repo-history extract ../../../.. --history-only --max-commits 300 -o /tmp/dashi-history.json
```

Earliest history (useful for the origin movie):

```bash
dashi-repo-history extract ../../../.. --history-only --first-commits 150 -o /tmp/dashi-early-history.json
```

Full semantic extraction is deliberately bounded first because the graph is large:

```bash
dashi-repo-history extract ../../../.. --max-commits 100 -o /tmp/dashi-semantic-history.json
```

A more legible first semantic film:

```bash
dashi-repo-history extract ../../../.. \
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
dashi-repo-history extract ../../../.. \
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
dashi-repo-history extract ../../../.. \
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
