# DASHI repository-history visualization frontend

`repo_history` is now a **visualization and compatibility frontend** for the
single DASHI repository-intelligence product.

The canonical product is `dashi-repo`, backed by one WAL SQLite database:

```text
.dashi/repository.sqlite3
```

There is no JSON handoff between repository discovery, Git/PR history,
narrative archaeology, or visualization.  The database owns persistent state;
plain-text CLI output is a view over that state.

## Ownership

The product boundary is deliberately split by authority, not by storage:

- `tools/agda_preflight` owns the canonical Agda Tree-sitter parser, structural
  interfaces, diagnostics, symbol/signature inventory, discovery, affected
  closure and the repository database.
- Git/PR harvesting writes commit topology, refs, touched paths and
  development-narrative rows into that same database.
- development narrative may guide discovery and explain intent, but cannot
  establish theorem truth, Agda proof validity, empirical truth or scientific
  authority.
- this package owns temporal scene compilation and rendering.
- Agda remains the final proof/type authority.

The old `dashi_repo_history.agda` frontend is retained only as a **legacy
parity/visualization adapter** while historical semantic-scene parity is
checked against the canonical repository-intelligence parser.  It is not the
normal indexing or agent-discovery path.

## Installation

Use one environment for the repository-intelligence core and visualization
frontend:

```bash
python -m pip install -e './tools/agda_preflight[test,mcp]'
python -m pip install -e './tools/visualization/repo_history[full]'
```

Both use the same Tree-sitter runtime line (`>=0.25,<0.27`).  `networkx` and
`manim` are visualization extras; they are not required by `dashi-repo` for
indexing, history, archaeology or MCP use.

## Bootstrap the repository database

```bash
dashi-repo bootstrap --root . --github-prs chboishabba/dashi_agda
```

That performs the canonical preflight-parser inventory and then stores complete
Git/PR development history in the same database.

Useful status/query commands:

```bash
dashi-repo status --root .
dashi-repo symbol FactorsThrough --root .
dashi-repo related FactorsThrough --root .
dashi-repo archaeology 'Balaban C3' --root .
dashi-repo frontier Casimir --root .
dashi-repo stale 'Balaban C3' --root .
dashi-repo discover certainlyMissingXYZ --root .
```

A categorical absence claim is allowed only when both the canonical semantic
inventory and complete development-history archaeology are fresh and empty for
the query.

## Compatibility commands

`dashi-repo-narrative` remains as a thin wrapper around the unified product for
older scripts.  `dashi-repo-history` retains the older scene/extraction surface
for parity and visualization work, but new repository intelligence should be
added to `dashi-repo`, not implemented here independently.

## Visualization dependencies

Install only when rendering is required:

```bash
python -m pip install -e './tools/visualization/repo_history[visualize]'
```

The visualization layer must consume repository-intelligence state rather than
becoming a second semantic authority.  Any legacy historical semantic parser
result is observational/parity evidence only until it matches the canonical
preflight-derived representation.

## Tests

```bash
pytest tools/agda_preflight/tests -q
pytest tools/visualization/repo_history/tests -q
```

The two suites are expected to run in the same virtual environment.
