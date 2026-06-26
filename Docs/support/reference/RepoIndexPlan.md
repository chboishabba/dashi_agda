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

### Global flags

```bash
--json              machine-readable output
--pretty            terminal output, default
--root <path>       repo root, default .
--index <path>      index file, default .repo-index/index.json
--depth <n>         graph/refs traversal depth
--kind <kind>       filter by symbol kind
--source <source>   agda | docs | py | all
```

`build` should materialize the index file and exit. Every other command should
read that file, and may fall back to source scanning only when the index is
missing or stale.

## Command Semantics

### `defs <symbol>`

Return the best definition match or matches for a symbol prefix or exact name.
Each match should include the definition site, module, kind, and a short
summary.

Pretty output:

```text
PsiProposalKind
  kind: data
  module: DASHI.Interop.PNFSpectralPhiPsiABICore
  file: DASHI/Interop/PNFSpectralPhiPsiABICore.agda:176
  status: candidate-only
  summary: Psi proposal row kinds over Phi. Candidate-only.
```

### `refs <symbol>`

Return typed references grouped by bucket. The command should report direct
uses, import uses, and doc mentions separately. If a reverse edge is unknown,
it should stay in `unknown` rather than being folded into a guess.

### `reqs <symbol>`

Return immediate requirements only:

- syntactic requirements: imports, fields, local dependencies
- semantic requirements: receipts, promotion boundaries, authority flags

This command should not become a transitive dependency dump in v1.

### `hover <symbol>`

Return a short editor-style summary. This is the human-facing compact form of
`defs` plus a little context, not a separate semantic source.

### `complete <prefix>`

Return symbol candidates beginning with the prefix, case-preserving, sorted by
stable relevance.

### `graph <symbol>`

Return a shallow dependency tree with reverse references. Use `--depth` to
expand the neighborhood.

### `status <symbol>`

Return explicit status only. If the repo does not encode a canonical status,
return `unknown`.

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

### JSON Envelope

Every JSON response should include:

```json
{
  "schema_version": "1.0.0",
  "command": "defs",
  "query": "PsiProposalKind",
  "root": ".",
  "index": ".repo-index/index.json",
  "matches": []
}
```

The exact payload shape after the envelope depends on the command, but
`schema_version`, `command`, `query`, `root`, and `index` should always be
present.

### Symbol Record

```json
{
  "symbol_id": "DASHI.Interop.PNFSpectralPhiPsiABICore.PsiProposalKind",
  "name": "PsiProposalKind",
  "kind": "data",
  "language": "agda",
  "module": "DASHI.Interop.PNFSpectralPhiPsiABICore",
  "file": "DASHI/Interop/PNFSpectralPhiPsiABICore.agda",
  "line_start": 176,
  "line_end": 184,
  "signature": "data PsiProposalKind : Set where ...",
  "snippet": "data PsiProposalKind : Set where ...",
  "doc": "Psi proposal row kinds over Phi.",
  "status": {
    "promotion": "candidate-only",
    "authority": "no-runtime-authority",
    "truth": "no-truth-promotion",
    "source": "agda"
  },
  "tags": [
    "PNF",
    "PhiPsi",
    "candidate-only",
    "interop"
  ]
}
```

### Reference Record

Refs should be typed.

```json
{
  "from_symbol": "DASHI.Interop.PNFSpectralFieldArchitectureReceipt.foo",
  "to_symbol": "DASHI.Interop.PNFSpectralPhiPsiABICore.PsiProposalKind",
  "ref_kind": "definition-use",
  "file": "DASHI/Interop/PNFSpectralFieldArchitectureReceipt.agda",
  "line": 697,
  "snippet": "... PsiProposalKind ..."
}
```

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

### Requirements Record

```json
{
  "symbol_id": "DASHI.Interop.PNFSpectralPhiPsiABICore.PsiProposalKind",
  "syntactic_requirements": [
    {
      "kind": "import",
      "symbol": "DASHI.Interop.PNFSpectralRebuildability",
      "source": "parsed-import"
    },
    {
      "kind": "field",
      "symbol": "PhiCoordinateTable",
      "source": "local-record-field"
    }
  ],
  "semantic_requirements": [
    {
      "kind": "receipt",
      "symbol": "PNFSpectralNumericABICoreReceipt",
      "status": "candidate-only",
      "source": "agda"
    },
    {
      "kind": "promotion-boundary",
      "value": "no-truth-promotion",
      "source": "agda"
    }
  ]
}
```

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

Status extraction priority:

1. Agda definitions, fields, constructors, and values
2. Agda imports and module names
3. Canonical receipt records
4. Docs cross-links
5. Prose fallback for search only

`pulledBack` should remain a derived label until the repo defines a canonical
Agda source for it.

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

## Minimal v1 Success Criterion

Given a symbol name, the tool can reliably answer:

- where it is defined
- where it is referenced
- what imports and local fields it depends on
- which receipts or authority flags it mentions
- whether explicit Agda-grounded status marks it candidate-only, promoted, or blocked
- which docs mention it
- what its immediate dependency graph looks like

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
- The index should stay usable without a live editor session.
