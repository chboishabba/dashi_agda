# DASHI repository intelligence

This package is the semantic core of the unified DASHI repository-intelligence
product.

Canonical interface:

```text
dashi-repo
  -> .dashi/repository.sqlite3
```

The product uses one SQLite/WAL database for repository semantics, preflight
state, Git/PR history, development narrative, provenance/status annotations and
promotion receipts.  Production subsystems do not exchange JSON files.

## Authority boundary

The repository-intelligence layer is deliberately non-elaborating.  It can
parse, index, resolve, compare and structurally diagnose Agda source, but it
**does not replace Agda**.  Agda remains the final type/proof authority.

Development narrative is a separate authority domain: PR and commit prose may
explain intent and guide archaeological discovery, but cannot establish theorem
truth, empirical truth or source authority.

## Canonical architecture

```text
Agda source
   |
   v
preflight Tree-sitter parser / resolver
   |
   +--> modules / imports / affected closure
   +--> symbols / signatures / bodies / refs
   +--> diagnostics / API fingerprints
   |
   v
.dashi/repository.sqlite3
   ^
   |
Git + PR harvest
   +--> commits / parent edges / refs / touched paths
   +--> PR membership
   +--> narrative/frontier/nonclaim/verification statements
```

There is one canonical Agda parser implementation: `tools/agda_preflight`.
The historical `scripts/repo_index.py` database is accepted only as a migration
source.  New whole-repository inventory is produced by `dashi-repo index` using
the preflight AST/interface parser.

The old `repo_history` Agda extractor remains only as an optional parity and
visualization adapter while historical scene parity is migrated; normal agent
search, indexing, history and MCP do not depend on it.

## Install

A single virtual environment can contain both the semantic core and the
visualization frontend:

```bash
python -m pip install -e './tools/agda_preflight[test,mcp]'
python -m pip install -e './tools/visualization/repo_history[full]'
```

Both use the same Tree-sitter runtime line (`>=0.25,<0.27`).

## Bootstrap

Build current repository semantics and complete development history into the
same database:

```bash
dashi-repo bootstrap --root . --github-prs chboishabba/dashi_agda
```

The two stages are also available separately:

```bash
dashi-repo index --root .
dashi-repo harvest --root . --github-prs chboishabba/dashi_agda
```

`index` preserves existing provenance tags and requirement annotations for
symbols that survive the rebuild.

`harvest` stores commit topology, parent edges, refs, touched paths, pull
requests and development narrative relationally.

For an existing checkout with the old `.repo-index/index.sqlite3` database:

```bash
dashi-repo sync-index --root .
```

That is a one-way compatibility import into normalized `repo_*` tables; it is
not the preferred producer.

## Discovery

```bash
dashi-repo symbol FactorsThrough --root .
dashi-repo related FactorsThrough --root .
dashi-repo object DASHI.Core.QueryFactorisationSufficiency.FactorsThrough --root .
dashi-repo discover 'finite spectral projector' --root .
dashi-repo lineage --prefix DASHI.Physics.Closure.NSTriadKN --root .
```

Normal search demotes modules containing `Round<digits>` to historical
snapshots.  `related` distinguishes exact/signature/body equivalence from
heuristic structural similarity; none of those labels manufacture Agda proof
equality.

A categorical negative discovery claim is fail-closed.  It is permitted only
when:

1. the native semantic inventory covers all canonical Agda files and is fresh;
2. no live, historical, equivalent or materially similar semantic candidate
   was found; and
3. a complete Git-development-history harvest exists and narrative archaeology
   found no related candidate.

Otherwise discovery reports `search_incomplete` or a candidate-bearing status.

## History and archaeology

```bash
dashi-repo history 'Balaban C3' --root .
dashi-repo archaeology 'Balaban C3' --root .
dashi-repo frontier Casimir --root .
dashi-repo stale 'Balaban C3' --root .
dashi-repo explain 'consumer sufficiency' --root .
```

These commands query development history already stored in the database.
`stale` is explicitly heuristic: it identifies older frontier language that a
later development event may have superseded.  It does not alter formal status.

## Structural preflight

The same product exposes the fast preflight loop:

```bash
dashi-repo diagnose DASHI/Biology/Everything.agda --root .
dashi-repo next DASHI/Biology/Everything.agda --require-fix --root .
dashi-repo affected DASHI/Core/Foo.agda --root .
dashi-repo refresh DASHI/Core/Foo.agda --root .
```

The checker may perform:

- Tree-sitter parsing and incremental syntax indexing;
- lexical/module scope resolution;
- import/open/using/hiding/renaming resolution;
- exported-symbol, record/data/constructor/projection indexing;
- telescope reconstruction and shallow type-shape propagation;
- bounded structural checks and trust-boundary diagnostics;
- dependency/API fingerprinting and reverse-affected closure.

It must not claim:

- general dependent unification or metavariable solving;
- arbitrary definitional equality/normalization;
- full universe/positivity/termination checking;
- cubical/path elaboration or reflection execution;
- proof validity.

## MCP

`dashi-repo-mcp` is the unified agent-facing server.  It extends the stable
preflight toolset with repository discovery and development-history tools.

The older `dashi-agda-mcp` command remains a compatibility surface with its
original tool contract.

## Compatibility commands

Existing `dashi-agda*` commands remain available while callers migrate.  New
repository-intelligence behavior should be added to `dashi-repo` rather than
creating another index/database/semantic service.

## Database policy

Persistent product state belongs in SQLite tables.  New repository-intelligence
features should extend the shared database with normalized tables rather than
introducing JSON caches or handoff files.

Legacy serialized cache columns may remain temporarily where required for
backward compatibility with older preflight requests, but they are not the
canonical repository/discovery/history model and should be retired behind
relational replacements rather than expanded.

## Tests

Run both packages in the same environment:

```bash
pytest tools/agda_preflight/tests -q
pytest tools/visualization/repo_history/tests -q
```

Then exercise the product boundary:

```bash
dashi-repo bootstrap --root . --github-prs chboishabba/dashi_agda
dashi-repo status --root .
dashi-repo discover certainlyMissingXYZ --root .
```
