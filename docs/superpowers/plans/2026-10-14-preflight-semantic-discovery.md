# Preflight Semantic Discovery Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task.

**Goal:** Extend DASHI Agda preflight with persistent symbol discovery, equivalence/similarity search, absence receipts, live-vs-history classification, and read-only RoundNNN lineage analysis.

**Architecture:** Reuse `source-index.sqlite3` as the single persistent substrate. Persist declaration/catalog rows derived from existing module interfaces, layer deterministic normalized fingerprints and lightweight similarity ranking over those rows, expose the features through `SourceIndex` -> `DashiAgdaService` -> CLI/MCP, and keep Round analysis read-only. Agda remains the final proof authority.

**Tech Stack:** Python 3, sqlite3/WAL, existing tree-sitter Agda preflight interfaces, pytest, existing CLI/MCP adapters.

**Spec:** `docs/superpowers/specs/2026-10-14-preflight-semantic-discovery-design.md`

## Global Constraints

- Extend the existing source index; do not create a second repository database.
- Warm read-only discovery must not parse source files.
- Exact/equivalent/similar are separate result classes; similarity never establishes proof equivalence.
- Historical RoundNNN modules are discoverable but demoted from default live search.
- Absence claims require an explicit discovery receipt.
- Round analysis is read-only in this tranche.

## Review Focus

- Old schema-v5 databases migrate without losing cached module/interface state.
- Interface JSON variants missing optional fields do not crash catalog refresh.
- Ambiguous unqualified names return all live candidates instead of selecting one silently.
- Similarity search remains deterministic and clearly labelled non-equivalent.
- Round parsing handles multiple `RoundNNN` occurrences and non-round modules without false lineage edges.

---

### Task 1: Persistent declaration catalogue

**Files:**
- Modify: `tools/agda_preflight/agda_preflight/source_index.py`
- Test: `tools/agda_preflight/tests/test_source_index.py`

**Interfaces:**
- Produces: `SourceIndex.search_symbols(query, *, include_history=False, limit=50) -> list[dict]`
- Produces: persisted declaration rows with exact name, qualified name, kind, signature, fingerprints, and surface role.

- [ ] Add failing schema migration/catalogue tests.
- [ ] Implement schema v6 declaration catalogue and lazy refresh from persisted `interface_json`.
- [ ] Add exact qualified/unqualified/suffix symbol lookup with live-first ordering.
- [ ] Verify focused tests.

### Task 2: Equivalent and structurally similar discovery

**Files:**
- Create: `tools/agda_preflight/agda_preflight/discovery.py`
- Modify: `tools/agda_preflight/agda_preflight/source_index.py`
- Test: `tools/agda_preflight/tests/test_discovery.py`

**Interfaces:**
- Produces: normalized text/signature/body fingerprints.
- Produces: `SourceIndex.related_symbols(symbol, *, include_history=False, limit=50) -> dict` with `exact`, `signature_equivalent`, and `similar` strata.

- [ ] Add failing normalization/ranking tests.
- [ ] Implement deterministic normalization and similarity ranking.
- [ ] Wire catalogue queries.
- [ ] Verify focused tests.

### Task 3: Discovery receipt and absence protocol

**Files:**
- Modify: `tools/agda_preflight/agda_preflight/source_index.py`
- Modify: `tools/agda_preflight/agda_preflight/service.py`
- Test: `tools/agda_preflight/tests/test_service.py`

**Interfaces:**
- Produces: `DashiAgdaService.discover(query, *, include_history=False, limit=50) -> dict`.
- Receipt contains query, canonical/live matches, related matches, historical matches, and `absence_claim_permitted`.

- [ ] Add failing service tests for partial/live/historical/no-match cases.
- [ ] Implement receipt generation without source parsing on warm index.
- [ ] Verify focused tests.

### Task 4: RoundNNN lineage and novelty report

**Files:**
- Create: `tools/agda_preflight/agda_preflight/lineage.py`
- Modify: `tools/agda_preflight/agda_preflight/source_index.py`
- Test: `tools/agda_preflight/tests/test_lineage.py`

**Interfaces:**
- Produces: `SourceIndex.round_lineage(prefix=None) -> dict`.
- Reports family, ordered rounds, declaration overlap, added/removed/signature-changed counts, novelty ratio, and snapshot-noise ratio.

- [ ] Add failing family extraction/delta tests.
- [ ] Implement deterministic RoundNNN family extraction and adjacent delta computation.
- [ ] Verify focused tests.

### Task 5: CLI and MCP exposure

**Files:**
- Modify: `tools/agda_preflight/agda_preflight/cli.py`
- Modify: `tools/agda_preflight/agda_preflight/mcp_server.py`
- Modify: `tools/agda_preflight/README.md`
- Test: existing CLI/MCP tests plus new discovery assertions.

**Interfaces:**
- CLI: `dashi-agda symbol`, `dashi-agda related`, `dashi-agda discover`, `dashi-agda lineage`.
- MCP: `symbol_search`, `related_symbols`, `discover`, `round_lineage`.

- [ ] Add failing command/adapter tests.
- [ ] Add CLI/service/MCP plumbing and JSON output.
- [ ] Document trust boundary and examples.
- [ ] Verify focused tests.

### Task 6: Regression verification

**Files:** no intended production changes.

- [ ] Run `pytest tools/agda_preflight/tests -q`.
- [ ] Run any existing preflight benchmark/regression commands available in the checkout.
- [ ] Confirm warm discovery queries parse zero files.
- [ ] Review diff for accidental theorem/source changes.
