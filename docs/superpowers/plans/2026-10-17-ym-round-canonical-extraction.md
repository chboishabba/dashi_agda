# Yang–Mills Round Canonical Extraction Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Contract the priority historical Yang–Mills `RoundNNN` lineages into dependency-aware semantic packages, classify each package against current non-Round mathematics, and expose only genuinely residual obligations through non-Round canonical owners while preserving provenance and keeping every Clay/YM promotion gate false.

**Architecture:** Tranche A is a read-only SQLite analysis pipeline layered on the existing stranded-analysis helpers. It first builds deterministic package records from Round ancestry and repeated frontier declarations, then classifies those packages against the full non-Round semantic universe. Tranche B consumes the resulting classifications to create a small fail-closed canonical residual surface and a generated JSONL extraction receipt; no Round source file is moved or deleted.

**Tech Stack:** Python 3, SQLite, existing `scripts/_stranded_common.py` helpers, pytest, Agda source modules, GitHub branch/PR workflow.

**Spec:** `docs/superpowers/specs/2026-10-17-ym-round-canonical-extraction-design.md`

## Global Constraints

- Round modules remain non-authoritative by default.
- The SQLite repository index is opened read-only by the new tooling.
- Body-only equality is never sufficient semantic equivalence evidence.
- Existing non-Round theorem owners and compilers are reused rather than duplicated.
- `sourceAttachmentCountIsEighteen`-style count/status receipts are never promoted as theorem authority.
- Negative/no-go results remain first-class extraction outcomes.
- No Round file is deleted, moved, or quarantined in this tranche.
- Source attribution remains attached to its existing owner; extraction does not manufacture proof authority.
- `clayYangMillsPromoted`, `clayPromotion`, and equivalent Clay completion gates remain false unless independently proved outside this extraction process.

## Review Focus

- Repeated Round declarations that change names/types slightly must collapse only when evidence supports one evolving obligation, never by fuzzy name alone.
- Existing non-Round compilers must classify historical targets as `CANONICAL_COMPILER_EXISTS` when only a selected same-object premise remains open.
- Reflexive counts and scheduler/status booleans must stay `STATUS_ONLY` even when they are unmatched signatures.
- Negative/firewall declarations must survive package contraction as `NEGATIVE_RESULT` and remain visible in receipts.
- Missing/ambiguous semantic evidence must fail closed as `UNRESOLVED`, never auto-promote to a canonical owner.

---

### Task 1: Target configuration and package-clustering core

**Files:**
- Create: `config/ym-round-extraction-targets.json`
- Create: `scripts/cluster_ym_round_packages.py`
- Create: `tests/test_ym_round_packages.py`

**Interfaces:**
- Consumes: `scripts/_stranded_common.py` (`connect`, `module_paths`, `load_import_graph`, `decls_for_modules`, `is_round`, `family_of`, stable hashing helpers as available).
- Produces: `load_targets(path: Path) -> dict`, `build_round_graph(imports, modules) -> tuple[dict[str,set[str]],dict[str,set[str]]]`, `cluster_packages(conn, cfg) -> list[dict]`, and deterministic JSONL output `.dashi/round-stranded/ym-package-clusters.jsonl`.

- [ ] **Step 1: Write failing tests for target loading, deterministic Round-family filtering, terminal-leaf detection, and stable package IDs.**

Tests must assert all nine seed families are present, non-YM and non-Round modules are excluded, repeated invocation yields identical package IDs/order, and a package contains terminal leaves plus ancestry metadata.

- [ ] **Step 2: Run focused tests and verify they fail because clustering functions/files do not yet exist.**

Run: `pytest tests/test_ym_round_packages.py -k 'targets or cluster or package_id' -v`

Expected: FAIL due to missing module/functions.

- [ ] **Step 3: Implement config and minimal deterministic clustering.**

`config/ym-round-extraction-targets.json` must declare schema version, target prefix, Round regex, nine seed families, candidate positive names, status/count names, disposition names, and output paths. `cluster_ym_round_packages.py` must open SQLite read-only, build Round parent/child relations, find terminal leaves, collect Round-only ancestry, collect declaration histories, group repeated frontier-enum/dependency-adjacent declarations conservatively, and emit stable-sorted package records.

- [ ] **Step 4: Run focused tests and verify pass.**

Run: `pytest tests/test_ym_round_packages.py -k 'targets or cluster or package_id' -v`

Expected: PASS.

- [ ] **Step 5: Commit Task 1.**

Commit message: `feat(ym): cluster historical Round obligation packages`

---

### Task 2: Package semantic classifier

**Files:**
- Create: `scripts/classify_ym_round_packages.py`
- Modify: `tests/test_ym_round_packages.py`

**Interfaces:**
- Consumes: package records from Task 1 plus the complete non-Round declaration universe from the repository index.
- Produces: `classify_package(package: dict, nonround_indexes: dict, cfg: dict) -> dict`, `classify_packages(conn, cfg, packages) -> list[dict]`, and final machine-readable package rows with one of `SUPERSEDED_EXACT`, `SUPERSEDED_RENAMED`, `CANONICAL_COMPILER_EXISTS`, `ALTERNATE_PROOF`, `NEGATIVE_RESULT`, `STATUS_ONLY`, `GENUINE_OPEN_OBLIGATION`, `UNRESOLVED`.

- [ ] **Step 1: Add failing tests for every disposition and evidence firewall.**

Tests must pin: exact match; same signature/different body alternate proof; explicit count/reflexivity status-only; negative/firewall preservation; canonical compiler with selected premise still open; renamed supersession requiring more than name similarity; body-only equality refusal; ambiguous cases returning `UNRESOLVED`.

- [ ] **Step 2: Run classifier-focused tests and verify they fail.**

Run: `pytest tests/test_ym_round_packages.py -k 'classification or superseded or compiler or status or negative or unresolved' -v`

Expected: FAIL because classifier is absent.

- [ ] **Step 3: Implement conservative semantic indexes and classifier.**

Use exact `(signature_sha256, body_sha256)`, signature-only, name, normalized role/conclusion evidence, dependency-neighborhood evidence, explicit forwarding/alias evidence where present, and current non-Round compiler/result relationships. Never treat body-only equality as semantic proof. Every nontrivial disposition must include `evidence` and `nonround_matches` fields.

- [ ] **Step 4: Run classifier tests and verify pass.**

Run: `pytest tests/test_ym_round_packages.py -k 'classification or superseded or compiler or status or negative or unresolved' -v`

Expected: PASS.

- [ ] **Step 5: Commit Task 2.**

Commit message: `feat(ym): classify Round packages against non-Round owners`

---

### Task 3: End-to-end extraction receipt generation

**Files:**
- Modify: `scripts/classify_ym_round_packages.py`
- Modify: `tests/test_ym_round_packages.py`
- Generate: `.dashi/round-stranded/ym-packages.jsonl`

**Interfaces:**
- Consumes: clusters and package classifications from Tasks 1–2.
- Produces: deterministic JSONL rows with package id, family, terminal leaves, Round ancestry, declaration names/fingerprints, semantic matches, disposition/evidence, retained negative results, unresolved residuals, selected canonical owner if any, and archive status in `{EXTRACTED,SUPERSEDED,NEGATIVE-RESULT,HISTORICAL-ONLY,UNRESOLVED}`.

- [ ] **Step 1: Add failing receipt-schema/determinism tests.**

Tests must assert stable ordering, required fields, valid archive-status mapping, no generated authority field for `STATUS_ONLY`, and preservation of unresolved/negative evidence.

- [ ] **Step 2: Run receipt tests and verify fail.**

Run: `pytest tests/test_ym_round_packages.py -k 'receipt or archive_status or deterministic_jsonl' -v`

Expected: FAIL.

- [ ] **Step 3: Implement JSONL writer and run it against the current index.**

Commands:
- `.venv/bin/python scripts/cluster_ym_round_packages.py`
- `.venv/bin/python scripts/classify_ym_round_packages.py`

Expected: `.dashi/round-stranded/ym-packages.jsonl` generated without modifying `.dashi/repository.sqlite3`.

- [ ] **Step 4: Run receipt tests and verify pass.**

Run: `pytest tests/test_ym_round_packages.py -k 'receipt or archive_status or deterministic_jsonl' -v`

Expected: PASS.

- [ ] **Step 5: Commit Task 3 including the generated receipt.**

Commit message: `feat(ym): emit canonical Round extraction receipts`

---

### Task 4: CMP109 source-semantics and physical transfer-gap canonical owners

**Files:**
- Create: `DASHI/Physics/YangMills/BalabanCMP109CanonicalSourceSemanticsObligationsExact.agda`
- Create: `DASHI/Physics/YangMills/BalabanCanonicalPhysicalTransferGapObligationExact.agda`
- Modify: `tests/test_ym_round_packages.py`

**Interfaces:**
- Consumes: classified package evidence for Round212–225 source-semantics families and current non-Round transfer-gap compiler owners.
- Produces: non-Round records/types that expose only residual same-object/source obligations and explicitly reuse existing generic compiler theorems.

- [ ] **Step 1: Add failing static tests that require both canonical module paths and forbid Round imports / promotion-true literals.**

Tests inspect source text and assert no `Round[0-9]+` imports, no assignment of Clay promotion gates to `true`, and presence of explicit residual-obligation fields rather than copied scheduler booleans.

- [ ] **Step 2: Run focused tests and verify fail because modules do not exist.**

Run: `pytest tests/test_ym_round_packages.py -k 'cmp109_owner or transfer_gap_owner' -v`

Expected: FAIL.

- [ ] **Step 3: Implement CMP109 canonical source-semantics owner.**

Reuse strongest current non-Round theorem types for generated-history response, beta-difference decomposition, and physical composite D1 chain-rule residuals where available. Do not create inhabitants from historical `open/blocked/closed` labels.

- [ ] **Step 4: Implement physical transfer-gap obligation owner.**

Import/reuse the existing non-Round clustering/OS4-to-`PositiveTransferGap` compiler and expose only the selected literal Balaban same-object premise(s) still needed to apply it. Do not duplicate the generic transfer-gap theorem.

- [ ] **Step 5: Run focused tests and verify pass.**

Run: `pytest tests/test_ym_round_packages.py -k 'cmp109_owner or transfer_gap_owner' -v`

Expected: PASS.

- [ ] **Step 6: Commit Task 4.**

Commit message: `feat(ym): contract CMP109 and transfer-gap residual owners`

---

### Task 5: CMP116 selected-term and trace/entropy canonical owners

**Files:**
- Create: `DASHI/Physics/YangMills/BalabanCMP116CanonicalSelectedTermReplayExact.agda`
- Create: `DASHI/Physics/YangMills/BalabanCMP116CanonicalTraceEntropyBudgetExact.agda`
- Modify: `tests/test_ym_round_packages.py`

**Interfaces:**
- Consumes: classified R409 selected-term replay and R429 trace/entropy budget packages.
- Produces: non-Round residual surfaces separating source provenance, executable replay, proof equality, exact compiler structure, quantitative analytic premises, and source-specific attachments.

- [ ] **Step 1: Add failing static tests for authority separation.**

Tests require explicit distinct fields/types for source/provenance vs proof-bearing equality in R409, and compiler/algebra vs analytic/source premises in R429; tests forbid Round imports and promotion-true literals.

- [ ] **Step 2: Run focused tests and verify fail.**

Run: `pytest tests/test_ym_round_packages.py -k 'r409_owner or r429_owner' -v`

Expected: FAIL.

- [ ] **Step 3: Implement R409 canonical selected-term replay owner.**

Expose separate source-transcription receipt, selected-term identity obligation, optional execution/replay receipt, and proof-bearing equality obligation. No execution receipt may inhabit theorem equality automatically.

- [ ] **Step 4: Implement R429 canonical trace/entropy budget owner.**

Reuse existing exact algebra/compiler owners when present; expose only residual quantitative inequalities and same-object source/measure/trace attachments.

- [ ] **Step 5: Run focused tests and verify pass.**

Run: `pytest tests/test_ym_round_packages.py -k 'r409_owner or r429_owner' -v`

Expected: PASS.

- [ ] **Step 6: Commit Task 5.**

Commit message: `feat(ym): contract CMP116 replay and entropy residual owners`

---

### Task 6: Canonical Clay residual and extraction receipt modules

**Files:**
- Create: `DASHI/Physics/YangMills/YangMillsCanonicalClayResidualExact.agda`
- Create: `DASHI/Physics/YangMills/YangMillsRoundExtractionReceiptExact.agda`
- Modify: `tests/test_ym_round_packages.py`

**Interfaces:**
- Consumes: canonical residual owner modules from Tasks 4–5 plus package receipt classifications.
- Produces: one non-Round terminal YM research scheduler with no Round theorem authority, and one formal extraction/provenance firewall module.

- [ ] **Step 1: Add failing static tests for terminal scheduler/firewall behavior.**

Tests require imports of the four canonical owner modules, forbid Round imports, require explicit false Clay-promotion receipts, require statements that extraction/status/supersession do not create theorem truth, and require retained negative/no-go provenance language/fields.

- [ ] **Step 2: Run focused tests and verify fail.**

Run: `pytest tests/test_ym_round_packages.py -k 'canonical_clay_residual or extraction_receipt' -v`

Expected: FAIL.

- [ ] **Step 3: Implement `YangMillsCanonicalClayResidualExact.agda`.**

Compose the canonical residual package types without manufacturing inhabitants. Expose the genuinely open source/theorem obligations as the preferred future YM max-cut surface. Keep all promotion booleans false.

- [ ] **Step 4: Implement `YangMillsRoundExtractionReceiptExact.agda`.**

Record that Round modules are historical by default; package extraction, supersession, status counts, source citations, and execution receipts do not create theorem authority; no archive/delete occurred; negative results remain preserved; Clay promotion remains false.

- [ ] **Step 5: Run focused tests and verify pass.**

Run: `pytest tests/test_ym_round_packages.py -k 'canonical_clay_residual or extraction_receipt' -v`

Expected: PASS.

- [ ] **Step 6: Commit Task 6.**

Commit message: `feat(ym): add canonical Clay residual extraction surface`

---

### Task 7: Full local-verification handoff and PR update

**Files:**
- Modify: PR #1229 description/comment only if needed; no authority code changes unless verification finds an issue.

**Interfaces:**
- Consumes: all preceding tasks.
- Produces: a branch ready for the user's local pytest, `dashi-agda-preflight`, index, and authority-gate verification.

- [ ] **Step 1: Run the complete Python test file.**

Run: `pytest tests/test_ym_round_packages.py -v`

Expected: PASS.

- [ ] **Step 2: Run existing stranded-tool regression tests.**

Run: `pytest tests/test_stranded_common.py -v`

Expected: PASS.

- [ ] **Step 3: Regenerate cluster/classification receipts and verify deterministic clean rerun.**

Run clustering/classification twice and confirm the generated `ym-packages.jsonl` bytes are unchanged.

- [ ] **Step 4: Perform source-level firewall scan.**

Check the six new Agda modules contain no `{!!}`, `postulate`, unsafe options, Round imports, or promotion gates set true.

- [ ] **Step 5: Fetch/compare branch head and update PR #1229 with implementation summary and explicit kernel boundary.**

State that connector-side source checks were performed, but do not claim Agda kernel-green status. Request the user's local `pytest`, `dashi-agda-preflight`, generated-receipt audit, and Clay-gate verification.

- [ ] **Step 6: Final implementation commit only if Task 7 required fixes.**

Commit message if needed: `fix(ym): harden Round extraction verification`
