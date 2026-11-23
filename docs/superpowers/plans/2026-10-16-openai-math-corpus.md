# OpenAI Math Corpus Agda Integration Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Record the pinned OpenAI mathematics corpus as an attribution-safe cross-prover source for Agda.

**Architecture:** Mirror only immutable upstream identity, cross-prover authority status, routing metadata and focused exports. Lean proof objects are never re-labelled as Agda proofs.

**Tech Stack:** Agda, Git/GitHub.

**Spec:** `docs/superpowers/specs/2026-10-16-openai-math-corpus-design.md`

## Global Constraints

- Pin `openai/math` exactly at `1581d4cbdd69a0faf34b2089614fe2a814316a6a`.
- Record upstream Lean toolchain exactly as `leanprover/lean4:v4.34.1`.
- Preserve Apache-2.0 attribution.
- Keep manuscript, upstream Lean and Agda theorem authority distinct.
- No kernel-green claim without execution evidence.

## Review Focus

- Cross-kernel theorem promotion must remain false by default.
- Relevance routing must not pay same-object transport.
- Upstream movement must not alter the pinned receipt.
- The focused rollup must not create a dependency on the upstream Lean environment.
- Regression assertions must match the production names exactly.

---

Execution method: native/inline; CI is not a blocker for this tranche.

### Task 1: Regression owner
- [x] Create `OpenAIMathCorpusRegression.agda` before production.
- [x] Preserve source-order RED boundary.

### Task 2: Upstream receipt
- [x] Create `OpenAIMathUpstreamReceiptExact.agda` with exact pin/toolchain/license and promotion-state vocabulary.

### Task 3: Priority atlas
- [x] Create `OpenAIMathPriorityAtlasExact.agda` with routing-only programme classifications.

### Task 4: Focused rollup
- [x] Create `DASHI/Research/OpenAIMath/Everything.agda`.

### Task 5: Repository export and PR
- [ ] Add the focused rollup to the nearest safe canonical research/global rollup.
- [ ] Audit exact pin and non-promotion boundaries.
- [ ] Open a draft PR with kernel-pending status.
