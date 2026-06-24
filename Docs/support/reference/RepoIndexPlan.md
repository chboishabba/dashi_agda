# Repo Index Plan

Declared surface level: `packaging`.

This document records the first product for repo-local discovery: a
mechanically reliable, Agda-grounded symbol index with completion semantics.
It is a query layer, not a planning DSL.

## Summary

The initial tool should answer symbol questions first:

- `defs`
- `refs`
- `reqs`
- `hover`
- `complete`
- `graph`
- `status`

The source of truth is the Agda repository itself. Agda LSP may be used to
enrich editor-facing behavior where it is available, but the repo index must
remain usable headless and must not depend on editor services for correctness.

## Core Split

```text
Discovery ≠ Planning ≠ Verification
```

- Discovery: repo-wide symbol graph, imports, references, requirements, docs
  links, and status surfaces.
- Planning: future agent-facing composition over indexed bundles.
- Verification: Agda typechecking, receipts, and promotion gates.

The first release only covers discovery plus minimal explicit status
extraction.

## What The Index Reads

Priority order for authority:

1. Agda definitions, records, fields, constructors, imports, and proof terms
2. Canonical receipt/status symbols already encoded in Agda
3. Module and file structure
4. Docs cross-links
5. Prose fallback for search only, never as authority

This avoids creating a second truth system beside Agda.

## Planned CLI Surface

```bash
repo-index build
repo-index defs <symbol>
repo-index refs <symbol>
repo-index reqs <symbol>
repo-index hover <symbol>
repo-index complete <prefix>
repo-index graph <symbol>
repo-index status <symbol>
```

`repo-lsp` may remain as a user-facing alias for the same command family.

### Output modes

- terminal-friendly pretty output
- JSON for agents and downstream tooling

## Data Model

The index should store, at minimum:

- symbol name and stable id
- defining file, line range, and module
- short snippet or hover text
- typed reference buckets
- local syntactic requirements
- semantic requirements exposed by Agda receipts or status records
- status flags derived from Agda-grounded fields
- doc cross-links

Reference buckets should stay typed, for example:

- `definition-use`
- `import-use`
- `doc-mention`
- `status-policy-mention`
- `test-use`
- `unknown`

Requirements should be split into:

- syntactic requirements: imports, fields, local dependencies
- semantic requirements: receipts, promotion boundaries, authority flags

## Status Handling

Status should be sparse and explicit. Prefer mechanically discoverable Agda
facts over prose inference.

Suggested canonical values:

- `promoted`
- `candidate-only`
- `blocked`
- `external-authority-required`
- `false-promotion`
- `deprecated`
- `unknown`

If the repo does not encode a canonical status, the index should return
`unknown` rather than guess.

## Build Order

1. Parse Agda module names and imports.
2. Extract symbol definitions and stable spans.
3. Implement `defs`, `hover`, and `complete`.
4. Extract typed references.
5. Derive immediate requirements.
6. Read explicit status/receipt fields from Agda surfaces.
7. Add docs cross-links.
8. Implement `graph`.
9. Generate bundle manifests from the index.
10. Only then consider any planning-layer syntax.

## Non-Goals For v1

- no new planning DSL
- no requirement to add source-embedded metadata blocks
- no dependence on Agda LSP for correctness
- no hand-authored bundle manifests as a second source of truth

## Assumptions

- Agda files remain the canonical source for project facts.
- `repo-index` is read-first and reproducible.
- Agda LSP, when present, is an enrichment layer only.
- Bundle generation will be downstream of the index, not parallel to it.

