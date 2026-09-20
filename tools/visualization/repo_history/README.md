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

Full repository (use bounded history first; the semantic graph is large):

```bash
dashi-repo-history extract ../../../.. --max-commits 100 -o /tmp/dashi-history.json
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
  --semantic --snapshot-index -1 --quality -qm
```

## Formal/implementation boundary

- Git or another version-state producer owns commit/candidate/workspace history.
- Tree-sitter owns syntactic observation; the resolver owns dependency admission.
- The semantic graph owns symbol identity and graph deltas.
- Manim owns only layout, camera movement, and animation realization.
- Ambiguous references remain explicit unresolved observations.

## Next extensions

- per-parent semantic deltas for merge commits,
- stable symbol identity across file moves/renames,
- expanded binder/application subgraphs,
- import-aware ambiguous-name resolution,
- persistent mental-map layout across commits,
- Casey candidate/workspace/build materializations,
- cross-repository semantic edges.
