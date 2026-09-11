# SLR Semantic Closure World Research Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Build one recurrent SLR world-research loop that computes multilingual canonical semantic closure and gaps, includes Simple English Wikipedia as a peer surface, and joins GWB/AU/Brexit tranche readiness without semantic promotion.

**Architecture:** Reuse the existing `sl.candidate_world_model.v0_1`, Wikimedia graph, source-role and multilingual artifacts. Canonical closure only unions language-independent atoms (QID, Wikidata Q/P edge, paid QID-to-QID wiki/world edge). Surface-local PNF atoms remain local until a canonical weld exists. Per-surface gaps generate attributed propagation views and next-acquisition obligations.

**Tech Stack:** Python 3, spaCy artifacts already produced by SLR, JSON/JSONL, MediaWiki/Wikidata cached receipts, Agda formal boundaries.

**Spec:** `docs/superpowers/specs/2026-09-11-slr-semantic-closure-world-research-design.md`

## Global Constraints

- Reuse SensibLaw CandidateWorldModel; do not create a parallel semantic carrier.
- Preserve append-only provenance.
- Propagated evidence must never imply the target article originally asserted the propagated fact.
- Shared QID must never imply translation or claim-semantic equivalence.
- Simple English Wikipedia is a peer evidence surface, not presumed to be a subset of English Wikipedia.
- AU may join as retained-source-ready; Brexit remains source-unpaid until retained narrative/source evidence exists.
- All outputs remain `candidate_only=true` and `semantic_promotion=false`.

---

### Task 1: Generic semantic atom / closure runtime

**Files:**
- Create: `tools/slr-discourse-reconstruct/slr_semantic_world_closure.py`
- Create: `tools/slr-discourse-reconstruct/run_semantic_world_closure.sh`

**Interfaces:**
- Consumes: `slr-wikimedia-world-follow-v1` graph, optional multilingual compatibility output.
- Produces: `slr-semantic-world-closure-v1` JSON with `canonical_atoms`, `surfaces`, `gaps`, `propagated_views`, and `acquisition_obligations`.

- [ ] **Step 1: Add fixture-free self-check mode** that constructs a tiny graph with two language surfaces and verifies a missing atom is propagated with `target_surface_asserted=false`.
- [ ] **Step 2: Run self-check** using `python3 ... --self-check`; expected exit 0 and `SLR_SEMANTIC_WORLD_CLOSURE_SELF_CHECK ... passed=true`.
- [ ] **Step 3: Implement canonical atom extraction** for QID, Wikidata property edges, and paid related-QID edges.
- [ ] **Step 4: Implement closure/gap/propagation computation** with deterministic IDs and source evidence lists.
- [ ] **Step 5: Implement acquisition obligations** for missing requested surfaces and unresolved local semantic atoms.
- [ ] **Step 6: Add shell runner** against existing GWB artifacts.
- [ ] **Step 7: Run self-check again** and commit.

### Task 2: Simple English Wikipedia peer surface

**Files:**
- Modify: `tools/slr-discourse-reconstruct/slr_multilingual_wikimedia_parser_compat.py`
- Modify: `tools/slr-discourse-reconstruct/run_multilingual_wikimedia_parser_compat.sh`

**Interfaces:**
- Consumes: existing reviewed root QIDs.
- Produces: multilingual compatibility rows where `simple` may appear exactly like any other language edition.

- [ ] **Step 1: Add `simple` parser mapping** using trained English parser semantics while retaining `language="simple"` surface provenance.
- [ ] **Step 2: Ensure sitelink key is `simplewiki`** and cache URL targets `simple.wikipedia.org`.
- [ ] **Step 3: Add receipt fields** `simplewiki_requested`, `simplewiki_surfaces`.
- [ ] **Step 4: Run existing multilingual diagnostic with `en,es,fr,de,simple`** and verify fallback semantics are not falsely reported as translation equivalence.
- [ ] **Step 5: Commit.**

### Task 3: Joined tranche readiness ABI

**Files:**
- Create: `tools/slr-discourse-reconstruct/slr_world_research_tranche_join.py`
- Create: `fixtures/slr/slr-world-research-tranches-v1.jsonl`

**Interfaces:**
- Consumes: tranche ledger plus optional GWB/AU/Brexit artifact paths.
- Produces: `slr-world-research-tranche-join-v1` with readiness states and no invented source evidence.

- [ ] **Step 1: Define three explicit states** `world-ready`, `retained-source-ready`, `source-unpaid`.
- [ ] **Step 2: Encode GWB/AU/Brexit current receipts** in the fixture.
- [ ] **Step 3: Implement validation** that `source-unpaid` tranches cannot contribute semantic atoms.
- [ ] **Step 4: Emit a joined tranche ledger** with each tranche's evidence references and next obligation.
- [ ] **Step 5: Add self-check** proving Brexit cannot become world-ready from the structured intent fixture alone.
- [ ] **Step 6: Commit.**

### Task 4: WorldResearchIteration orchestration

**Files:**
- Create: `tools/slr-discourse-reconstruct/run_world_research_iteration.sh`
- Modify: `tools/slr-discourse-reconstruct/run_gwb_wikimedia_world_follow.sh`
- Modify: `tools/slr-discourse-reconstruct/package_gwb_world_handoff.sh`

**Interfaces:**
- Consumes: current world artifacts, tranche ledger, multilingual surfaces.
- Produces: one iteration directory containing closure, gaps, propagation views, tranche join, and next-acquisition obligations.

- [ ] **Step 1: Run tranche join.**
- [ ] **Step 2: Run multilingual surface acquisition including Simple English when enabled.**
- [ ] **Step 3: Run semantic closure.**
- [ ] **Step 4: Emit `WORLD_RESEARCH_ITERATION_RECEIPT`** with atom/gap/obligation/tranche counts.
- [ ] **Step 5: Make GWB opt-in runner call this orchestrator after existing graph/source-role stages.**
- [ ] **Step 6: Include iteration outputs in v2 handoff without embedding article text.**
- [ ] **Step 7: Commit.**

### Task 5: Formal semantic closure and tranche boundaries

**Files:**
- Create: `DASHI/Interop/SLRSemanticWorldClosureExact.agda`
- Create: `DASHI/Interop/SLRWorldResearchTrancheConvergenceExact.agda`
- Modify: `DASHI/Interop/Everything.agda`
- Modify: `DASHI/Interop/SLRGWBExecutionRoadmapExact.agda`
- Modify: `DASHI/Interop/SLRWorldModelSuiteConvergenceRoadmapExact.agda`

**Interfaces:**
- Consumes: existing Wikimedia, multilingual, source-role, CandidateWorldModel boundaries.
- Produces: typed firewalls for semantic propagation, per-surface gaps, tranche readiness, and iterative acquisition.

- [ ] **Step 1: Formalize `SemanticAtomKind`, `SurfaceObservation`, `PropagatedEvidenceView`, `SemanticGap`, and `WorldResearchIterationBoundary`.**
- [ ] **Step 2: Prove by empty types** that propagation cannot rewrite source assertion, same QID cannot create semantic equivalence, and source-unpaid tranche cannot contribute world truth.
- [ ] **Step 3: Formalize tranche readiness coordinates for GWB/AU/Brexit.**
- [ ] **Step 4: Export both owners from `Everything.agda`.**
- [ ] **Step 5: Update roadmaps** to make semantic closure/world iteration active and multilingual PNF role compatibility paid.
- [ ] **Step 6: Run focused Agda checks** for the new owners and roadmaps.
- [ ] **Step 7: Commit.**

### Task 6: End-to-end validation

**Files:**
- No new source files expected.

**Interfaces:**
- Consumes: existing `/tmp/slr-validation-20260911` artifacts.
- Produces: runtime receipts and refreshed replayable handoff.

- [ ] **Step 1: Run `run_world_research_iteration.sh`** against existing GWB world artifacts.
- [ ] **Step 2: Confirm Simple English is either present with its own surface rows or explicitly absent as a surface obligation.**
- [ ] **Step 3: Confirm propagated views all have `target_surface_asserted=false`.**
- [ ] **Step 4: Confirm AU is retained-source-ready and Brexit source-unpaid.**
- [ ] **Step 5: Run focused Agda checks.**
- [ ] **Step 6: Repackage v2 handoff and verify checksum.**
