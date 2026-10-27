# Navier–Stokes Round Canonical Extraction Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Contract the full historical Navier–Stokes Round domain into an auditable, failure-closed non-Round canonical residual surface without changing theorem authority or Clay promotion state.

**Architecture:** Execute four tranches in order: authority hygiene, shared extraction engine/full NS classification, evidence-driven canonical owner extraction, then the terminal residual scheduler and receipts. The critical gate is after classification: Tranche C owner names and theorem surfaces are derived from the generated evidence and may not be invented in advance.

**Tech Stack:** Python 3, pytest, SQLite read-only repository index, Agda source modules, `dashi-agda-preflight`, existing `_stranded_common.py` and YM extraction scripts.

**Spec:** `docs/superpowers/specs/2026-10-17-ns-round-canonical-extraction-design.md`

## Global Constraints

- Base implementation branch: `chatgpt/ns-round-canonical-extraction`, originally branched from `2307adf73d29f825becd576673abc15573fe94f7`.
- Replace only the stale NS canonical root `DASHI.Physics.Closure.NSLiteralClayABCDCapstone` with `DASHI.Physics.Closure.NSConcreteLiteralClayABCDRunTargetExact`; do not add `NSClayOfficialSemanticPromotionBoundaryExact` as a second root.
- Preserve `rounds_authoritative_by_default = false` and `body_only_equivalence_is_semantic_evidence = false`.
- Discover all Round families under `DASHI.Physics.Closure.` and `DASHI.Papers.NavierStokes.`; priority hints may rank but never exclude families.
- Keep existing YM CLI entry points and established disposition semantics behaviorally compatible; receipt changes may be additive only.
- `UNRESOLVED` remains fail-closed and must never be counted as discharged.
- New canonical owners use `{-# OPTIONS --safe #-}` wherever mathematically possible, with zero Round theorem-authority imports, zero `postulate`, zero `{!!}`, and zero `--allow-unsolved-metas`.
- Same-object/source attachment predicates and reference objects must be externally fixed parameters, never inhabitant-selected record fields.
- Unsafe/postulated realizations must live in explicit non-safe bridges; receipts must state the relative axiom boundary.
- No citation, status Bool, generated receipt, hash, replay, or filename/name match is theorem evidence.
- Preserve source attribution according to `Docs/SourceAttributionPolicy.md`; repo-native contraction/interfaces are DASHI extensions.
- `clayNavierStokesPromoted = false` and `clayPromotion = false` throughout this tranche.
- Do not delete, move, or quarantine Round modules.
- Do not claim pytest, semantic-preflight, or Agda success without fresh command output from the environment that ran it.

## Review Focus

1. **Root reachability still enters Round modules indirectly.** Tests must verify the configured NS authority root and the literal theorem owner no longer depend on Round523 for coordinate authority.
2. **Multi-prefix discovery accidentally misses a family or double-counts one.** Tests must cover both prefixes, overlapping discovery, and full-family inclusion without seeds.
3. **Common/trivial signatures swamp semantic matches.** Tests must pin uncapped `nonround_match_count`, deterministic capped samples, and correct truncation flags.
4. **Generalizing the engine changes YM results or package IDs.** YM regression tests must compare wrapper outputs and ID namespace behavior before and after factoring.
5. **Residual records can pay obligations vacuously.** Canonical extraction tests must reject source/attachment/reference predicates as record fields and preserve false promotion gates.

---

## File Structure

### Shared extraction machinery

- Create: `scripts/_round_package_extraction.py` — domain-neutral clustering, semantic-match indexing, receipt sampling, deterministic serialization, archive-status helpers.
- Modify: `scripts/cluster_ym_round_packages.py` — compatibility wrapper over shared engine.
- Modify: `scripts/classify_ym_round_packages.py` — compatibility wrapper over shared engine/classification helpers.
- Create: `config/ns-round-extraction-targets.json` — NS prefixes, package namespace, classifier hints, outputs, sample cap.
- Create: `scripts/cluster_ns_round_packages.py` — NS clustering CLI wrapper.
- Create: `scripts/classify_ns_round_packages.py` — NS classification CLI wrapper.

### Authority and canonical Agda surfaces

- Modify: `.dashi/canonical-roots.json` — stale-root replacement only.
- Create: `DASHI/Physics/Closure/NSClayForcedBreakdownSourceCoordinatesExact.agda` — non-Round owner of C/D source-coordinate audit facts.
- Modify: `DASHI/Physics/Closure/NSClayLiteralABCDExact.agda` — consume the non-Round coordinate owner instead of Round523.
- Create later from evidence: one or more `DASHI/Physics/Closure/NSCanonical...Exact.agda` owners for genuine live obligations only.
- Create: `DASHI/Physics/Closure/NSCanonicalClayResidualExact.agda` — terminal residual scheduler.
- Create: `DASHI/Physics/Closure/NSRoundExtractionReceiptExact.agda` — typed authority receipt.

### Generated and test artifacts

- Generate locally from the full index: `.dashi/round-stranded/ns-packages.jsonl`.
- Create: `tests/test_ns_round_packages.py` — shared-engine and NS package/classifier tests.
- Create: `tests/test_ns_canonical_extraction.py` — root/authority/safety/scheduler tests.
- Modify: `tests/test_ym_round_packages.py` — additive regression assertions for shared engine and evidence-count fields where needed.

---

### Task 1: Authority-root hygiene and C/D coordinate extraction

**Files:**
- Modify: `.dashi/canonical-roots.json`
- Create: `DASHI/Physics/Closure/NSClayForcedBreakdownSourceCoordinatesExact.agda`
- Modify: `DASHI/Physics/Closure/NSClayLiteralABCDExact.agda`
- Create: `tests/test_ns_canonical_extraction.py`

**Interfaces:**
- Consumes: current `NSClayLiteralABCDExact` C/D coordinate checks and current `.dashi/canonical-roots.json`.
- Produces: a real non-Round NS authority root plus a non-Round coordinate owner with the same coordinate distinctions consumed by `NSClayLiteralABCDExact`.

- [ ] **Step 1: Write failing root/authority tests**

Add tests asserting:

```python
def test_ns_canonical_root_is_concrete_nonround_run_target():
    roots = load_roots()
    assert "DASHI.Physics.Closure.NSConcreteLiteralClayABCDRunTargetExact" in roots
    assert "DASHI.Physics.Closure.NSLiteralClayABCDCapstone" not in roots
    assert "DASHI.Physics.Closure.NSClayOfficialSemanticPromotionBoundaryExact" not in roots
```

and:

```python
def test_literal_abcd_uses_nonround_forced_breakdown_coordinates():
    text = read("DASHI/Physics/Closure/NSClayLiteralABCDExact.agda")
    assert "NSClayForcedBreakdownSourceCoordinatesExact" in text
    assert "NSTriadKNClayForcedBreakdownFormulationRound523Exact" not in import_lines(text)
```

Also assert the new coordinate owner contains no Round import, holes, postulates, or unsolved-meta option.

- [ ] **Step 2: Run the focused tests and verify RED**

Run:

```bash
pytest tests/test_ns_canonical_extraction.py -v
```

Expected: failures because the root is stale and the non-Round coordinate owner does not exist.

- [ ] **Step 3: Replace the stale root**

Edit `.dashi/canonical-roots.json` by replacing exactly:

```text
DASHI.Physics.Closure.NSLiteralClayABCDCapstone
```

with:

```text
DASHI.Physics.Closure.NSConcreteLiteralClayABCDRunTargetExact
```

Do not alter the existing policy object and do not add a second NS root.

- [ ] **Step 4: Extract the Round523 coordinate surface into a non-Round owner**

Create `NSClayForcedBreakdownSourceCoordinatesExact.agda` with the minimum coordinate datatype/functions needed by the existing C/D assertions. Preserve current coordinate names/semantics where practical so `NSClayLiteralABCDExact` changes only its owner alias/import, not theorem types.

If Round523 depends on unsafe/postulated modules, do not copy those imports into a safe module; instead parameterize the canonical coordinate owner over externally fixed coordinate evidence and defer concrete realization to a separate bridge task only if classification later proves one is needed.

- [ ] **Step 5: Rewire `NSClayLiteralABCDExact`**

Replace its Round523 import with the new non-Round owner and update only the coordinate-check references. Do not alter A/B/C/D carrier or theorem signatures.

- [ ] **Step 6: Run focused tests**

Run:

```bash
pytest tests/test_ns_canonical_extraction.py -v
```

Expected: root and Round523-import tests pass.

- [ ] **Step 7: Run semantic preflight on the authority files**

Run:

```bash
dashi-agda-preflight --root . --errors-only \
  DASHI/Physics/Closure/NSClayForcedBreakdownSourceCoordinatesExact.agda \
  DASHI/Physics/Closure/NSClayLiteralABCDExact.agda
```

If the local CLI does not accept file arguments, run the repository-supported focused equivalent and record the exact command/output.

- [ ] **Step 8: Commit**

```bash
git add .dashi/canonical-roots.json \
  DASHI/Physics/Closure/NSClayForcedBreakdownSourceCoordinatesExact.agda \
  DASHI/Physics/Closure/NSClayLiteralABCDExact.agda \
  tests/test_ns_canonical_extraction.py
git commit -m "feat(ns): clean canonical authority roots"
```

---

### Task 2: Factor a domain-neutral Round package engine without changing YM behavior

**Files:**
- Create: `scripts/_round_package_extraction.py`
- Modify: `scripts/cluster_ym_round_packages.py`
- Modify: `scripts/classify_ym_round_packages.py`
- Modify: `tests/test_ym_round_packages.py`

**Interfaces:**
- Produces reusable functions for config validation, prefix/family discovery, Round graph traversal, package clustering, non-Round indexing, bounded match rendering, receipt serialization, and archive-status mapping.
- Existing YM wrappers retain their current CLI defaults and `ym-round-package` ID namespace.

- [ ] **Step 1: Add failing YM compatibility tests**

Pin at least:

```python
def test_ym_wrapper_keeps_package_namespace_and_cli_defaults(): ...
def test_shared_engine_preserves_ym_cluster_shape(): ...
def test_shared_match_sampling_reports_full_count(): ...
```

For match sampling, construct more than 10 semantic matches and assert:

```python
assert row["nonround_match_count"] == total
assert len(row["nonround_matches"]) == 10
assert row["nonround_matches_truncated"] is True
```

- [ ] **Step 2: Run YM tests and verify RED for additive fields/shared module**

Run:

```bash
pytest tests/test_ym_round_packages.py -v
```

Expected: new tests fail because `_round_package_extraction.py` and additive match-count fields do not exist.

- [ ] **Step 3: Implement the shared engine**

Create `scripts/_round_package_extraction.py` with focused public helpers, including these stable interfaces:

```python
def discover_round_modules(paths: dict[str, str], prefixes: tuple[str, ...]) -> set[str]: ...
def build_round_graph(imports, modules): ...
def cluster_packages(conn, cfg: dict) -> list[dict]: ...
def build_nonround_indexes(conn, cfg: dict) -> dict: ...
def bounded_matches(matches: list[dict], limit: int) -> tuple[int, list[dict], bool]: ...
def write_jsonl(rows: list[dict], out: Path) -> None: ...
```

`cluster_packages` must use `cfg["package_namespace"]` when calling `stable_id` and must derive families from all discovered Round modules unless an explicit compatibility `seed_families` list is present for YM.

- [ ] **Step 4: Convert YM scripts into thin compatibility wrappers**

Keep current YM defaults:

```text
config/ym-round-extraction-targets.json
.dashi/round-stranded/ym-clusters.jsonl
.dashi/round-stranded/ym-packages.jsonl
```

and preserve existing classification semantics. Only additive receipt fields may change.

- [ ] **Step 5: Run YM regression tests**

Run:

```bash
pytest tests/test_ym_round_packages.py tests/test_stranded_common.py -v
```

Expected: all existing and new YM tests pass.

- [ ] **Step 6: Commit**

```bash
git add scripts/_round_package_extraction.py \
  scripts/cluster_ym_round_packages.py \
  scripts/classify_ym_round_packages.py \
  tests/test_ym_round_packages.py
git commit -m "refactor(round): share package extraction engine"
```

---

### Task 3: Add full-domain NS clustering and classification wrappers

**Files:**
- Create: `config/ns-round-extraction-targets.json`
- Create: `scripts/cluster_ns_round_packages.py`
- Create: `scripts/classify_ns_round_packages.py`
- Create/extend: `tests/test_ns_round_packages.py`

**Interfaces:**
- NS config supplies:
  - `target_prefixes = ["DASHI.Physics.Closure.", "DASHI.Papers.NavierStokes."]`
  - `package_namespace = "ns-round-package"`
  - no restrictive `seed_families`
  - `nonround_match_sample_limit = 10`
  - output paths for NS clusters/packages.
- NS wrappers call the shared engine and add only NS-specific classification hints.

- [ ] **Step 1: Write failing multi-prefix/full-family tests**

Cover:

```python
def test_ns_discovers_round_families_under_both_prefixes_without_seeds(): ...
def test_ns_package_ids_use_ns_namespace_and_are_deterministic(): ...
def test_ns_body_only_match_fails_closed(): ...
def test_ns_unresolved_remains_unresolved(): ...
def test_ns_negative_and_status_receipts_are_preserved(): ...
def test_ns_match_sampling_keeps_full_count_and_truncation_flag(): ...
```

Add a fixture where two modules are reachable under different prefixes and ensure both become packages exactly once.

- [ ] **Step 2: Run NS package tests and verify RED**

Run:

```bash
pytest tests/test_ns_round_packages.py -v
```

Expected: FAIL because config/wrappers do not exist.

- [ ] **Step 3: Add `config/ns-round-extraction-targets.json`**

Include exact prefixes, namespace, sample limit, output paths, status/negative hints, and optional `priority_families` that affect ranking only.

- [ ] **Step 4: Implement `cluster_ns_round_packages.py`**

Expose the same command shape as YM with NS defaults:

```text
--db .dashi/repository.sqlite3
--config config/ns-round-extraction-targets.json
--out <optional override>
```

- [ ] **Step 5: Implement `classify_ns_round_packages.py`**

Reuse shared semantic indexes and disposition logic. Support the base dispositions plus evidence-gated `CANONICAL_ENDPOINT` and `PROVENANCE_ONLY`; filename/name similarity alone must never produce either.

- [ ] **Step 6: Run NS and YM tests together**

Run:

```bash
pytest tests/test_ns_round_packages.py tests/test_ym_round_packages.py tests/test_stranded_common.py -v
```

Expected: PASS.

- [ ] **Step 7: Commit**

```bash
git add config/ns-round-extraction-targets.json \
  scripts/cluster_ns_round_packages.py \
  scripts/classify_ns_round_packages.py \
  tests/test_ns_round_packages.py
git commit -m "feat(ns): add full-domain Round classification"
```

---

### Task 4: Generate the full NS receipts and establish the evidence gate

**Files:**
- Generate: `.dashi/round-stranded/ns-clusters.jsonl` if configured as an intermediate artifact.
- Generate: `.dashi/round-stranded/ns-packages.jsonl`
- Optional generated summary: `.dashi/round-stranded/ns-package-summary.json`

**Interfaces:**
- Consumes the user's current full `.dashi/repository.sqlite3`.
- Produces the authoritative classification evidence used to define Tranche C owners.

- [ ] **Step 1: Re-index if the branch changed indexed source inputs**

Use the repository's current indexing command so the SQLite database reflects Tranche A source changes before classification.

Record the indexed file count, symbol count, and parse-error count.

- [ ] **Step 2: Generate NS clusters**

Run:

```bash
.venv/bin/python scripts/cluster_ns_round_packages.py
```

Expected: deterministic package-cluster artifact across both prefixes.

- [ ] **Step 3: Generate classified NS package receipts**

Run:

```bash
.venv/bin/python scripts/classify_ns_round_packages.py
```

Expected: `.dashi/round-stranded/ns-packages.jsonl` with every discovered package carrying a disposition and the three match-evidence fields.

- [ ] **Step 4: Validate receipt invariants**

Run a focused Python/pytest check asserting:

```text
sum(disposition counts) == total package rows
nonround_match_count >= len(nonround_matches) for every row
nonround_matches_truncated == (nonround_match_count > len(nonround_matches))
UNRESOLVED rows remain unresolved and have no fabricated owner
no generated row treats body-only evidence as supersession
```

- [ ] **Step 5: Produce the classification review summary**

Report at least:

```text
total package count
package count by disposition
package count by family/prefix
genuine-open count
unresolved count
negative-result count
status/provenance-only count
canonical-endpoint/compiler-covered count
top genuine-open/unresolved families and terminal leaves
```

Do not phrase the result as “2,236 -> N obligations” when unresolved packages remain.

- [ ] **Step 6: Evidence-review gate — STOP before Tranche C**

Inspect every `GENUINE_OPEN_OBLIGATION` package and the highest-value `UNRESOLVED` packages. Determine which can be:

```text
reclassified from stronger non-Round evidence,
merged into one theorem package,
represented by an existing owner,
or require a new canonical owner.
```

**Do not create Tranche C owner modules until this review determines exact owner names, theorem types, and blocker classes.** If the evidence reveals a substantially different architecture than the approved categories, update the design/plan before implementation.

- [ ] **Step 7: Commit generated receipts and any deterministic summary that repository policy keeps tracked**

```bash
git add .dashi/round-stranded/ns-packages.jsonl
# add cluster/summary artifacts only if they are intended tracked outputs
git commit -m "data(ns): record Round package classification"
```

---

### Task 5: Extract evidence-backed canonical NS residual owners

**Files:**
- Create/modify only the `DASHI/Physics/Closure/NSCanonical...Exact.agda` modules selected by Task 4 evidence.
- Create explicit `...BridgeExact.agda` modules only where a useful realization depends on unsafe/postulated infrastructure.
- Extend: `tests/test_ns_canonical_extraction.py`

**Interfaces:**
- Consumes: exact package IDs, blocker types, existing canonical compilers, and selected source/carrier objects documented at the Task 4 evidence gate.
- Produces: one non-Round canonical owner per genuinely distinct live obligation package, with no duplicate theorem ownership.

- [ ] **Step 1: Write one failing contract per selected owner**

For each owner selected from evidence, add tests pinning:

```text
module exists under a non-Round path
no Round import lines
safe owner contains no postulate/hole/unsolved-meta option
source/attachment predicates are parameters, not fields
reference object / target equality is externally fixed
compiler/output receipts cannot inhabit the residual
source attribution or DASHI-extension disclaimer is present
```

Where an unsafe bridge is needed, assert the safe owner does not import it.

- [ ] **Step 2: Run canonical extraction tests and verify RED**

Run:

```bash
pytest tests/test_ns_canonical_extraction.py -v
```

Expected: failure for each not-yet-created owner/interface.

- [ ] **Step 3: Implement the minimal safe owner for each evidence-backed package**

Use the exact owner/type names fixed during Task 4 review. Reuse existing non-Round compilers rather than reproducing historical Round proofs. Separate:

```text
already-proved compiler theorem
same-object/source attachment
quantitative analytic estimate
transport equality
source reconstruction
negative/no-go constraint
```

into distinct parameters/evidence where required.

- [ ] **Step 4: Add explicit non-safe bridges only where necessary**

A bridge may import postulated/unsafe infrastructure, but must have a name that exposes that boundary and must not be imported by the safe terminal scheduler.

Add a typed Bool/equality receipt if the distinction “paid relative to X, not unconditionally” is part of the surviving frontier.

- [ ] **Step 5: Run focused pytest and semantic preflight**

Run:

```bash
pytest tests/test_ns_canonical_extraction.py -v
dashi-agda-preflight --root . --errors-only
```

Record any warnings separately; do not reinterpret warnings as kernel evidence.

- [ ] **Step 6: Commit owners in coherent theorem packages**

Use one commit per independently reviewable owner/package, for example:

```text
feat(ns): extract canonical commutator residual
feat(ns): extract literal R406 transport residual
feat(ns): extract strict-margin residual
```

Actual commit names must follow the evidence-selected owner set rather than these examples.

---

### Task 6: Add the typed extraction receipt

**Files:**
- Create: `DASHI/Physics/Closure/NSRoundExtractionReceiptExact.agda`
- Extend: `tests/test_ns_canonical_extraction.py`

**Interfaces:**
- Produces the typed non-authority policy surface consumed by review/docs, not theorem proofs.

- [ ] **Step 1: Write the failing receipt test**

Assert the module contains exactly the required authority states:

```text
roundsAuthoritativeByDefault = false
extractionCreatesTheoremTruth = false
statusCountsAreClayPayments = false
negativeResultsPreserved = true
unresolvedPackagesCountAsDischarged = false
roundFilesArchivedOrDeleted = false
clayPromotion = false
```

Also assert it has no Round import, postulate, hole, or unsafe option.

- [ ] **Step 2: Run the focused test and verify RED**

Run:

```bash
pytest tests/test_ns_canonical_extraction.py -k round_extraction_receipt -v
```

- [ ] **Step 3: Implement `NSRoundExtractionReceiptExact.agda`**

Use `Bool` values plus `refl` equalities for the failure-closed invariants. Label the module as repository-native DASHI authority bookkeeping.

- [ ] **Step 4: Run focused tests/preflight**

Run:

```bash
pytest tests/test_ns_canonical_extraction.py -k round_extraction_receipt -v
dashi-agda-preflight --root . --errors-only
```

- [ ] **Step 5: Commit**

```bash
git add DASHI/Physics/Closure/NSRoundExtractionReceiptExact.agda \
  tests/test_ns_canonical_extraction.py
git commit -m "feat(ns): add Round extraction authority receipt"
```

---

### Task 7: Build the terminal `NSCanonicalClayResidualExact` scheduler

**Files:**
- Create: `DASHI/Physics/Closure/NSCanonicalClayResidualExact.agda`
- Extend: `tests/test_ns_canonical_extraction.py`

**Interfaces:**
- Consumes only evidence-backed non-Round canonical owners from Task 5 and existing canonical concrete theorem/semantic surfaces.
- Produces one failure-closed research scheduler describing the remaining typed NS frontier.

- [ ] **Step 1: Write failing scheduler tests**

Pin:

```python
def test_ns_terminal_scheduler_imports_only_nonround_canonical_owners(): ...
def test_ns_terminal_scheduler_uses_qualified_only_imports_for_overlapping_gate_names(): ...
def test_ns_terminal_scheduler_has_externally_fixed_residual_parameters(): ...
def test_ns_terminal_scheduler_preserves_false_clay_gates(): ...
```

Assert literal strings:

```text
clayNavierStokesPromoted = false
clayPromotion = false
```

- [ ] **Step 2: Run scheduler tests and verify RED**

Run:

```bash
pytest tests/test_ns_canonical_extraction.py -k terminal_scheduler -v
```

- [ ] **Step 3: Implement `NSCanonicalClayResidualExact.agda`**

Use qualified-only imports (`as Alias using ()`) for owners exposing overlapping gate/status names. The record should contain only the surviving evidence-backed residuals; it must not duplicate the historical scheduler or include all unresolved packages as fake theorem fields.

The scheduler is a research frontier, not a path that constructs `NSConcreteLiteralClayABCDRunTargetExact` without an actual A/B/C/D proof term.

- [ ] **Step 4: Run focused tests/preflight**

Run:

```bash
pytest tests/test_ns_canonical_extraction.py -k terminal_scheduler -v
dashi-agda-preflight --root . --errors-only
```

- [ ] **Step 5: Commit**

```bash
git add DASHI/Physics/Closure/NSCanonicalClayResidualExact.agda \
  tests/test_ns_canonical_extraction.py
git commit -m "feat(ns): add canonical Clay residual scheduler"
```

---

### Task 8: Full regression, receipt audit, and PR handoff

**Files:**
- No new production files expected unless verification exposes a bug.
- May update generated `.dashi/round-stranded/ns-packages.jsonl` after the final index refresh if canonical-owner additions change semantic matches.

**Interfaces:**
- Produces the final branch handoff with reproducible local verification commands and an honest classification summary.

- [ ] **Step 1: Refresh the repository index after all source changes**

Run the repo's current index command, record file/symbol/parse-error counts, then regenerate:

```bash
.venv/bin/python scripts/cluster_ns_round_packages.py
.venv/bin/python scripts/classify_ns_round_packages.py
```

If the final classification changes because Task 5 owners now match historical packages, commit the regenerated `ns-packages.jsonl` and report the before/after disposition delta.

- [ ] **Step 2: Run the complete relevant pytest suite**

Run:

```bash
pytest \
  tests/test_ns_round_packages.py \
  tests/test_ns_canonical_extraction.py \
  tests/test_ym_round_packages.py \
  tests/test_ym_cmp109_residual_instantiation.py \
  tests/test_ym_cmp116_residual_contraction.py \
  tests/test_stranded_common.py -v
```

Expected: zero failures.

Then run the repository's full `pytest` command if practical, as required by the TDD/verification workflow; report any unrelated failures by name rather than omitting them.

- [ ] **Step 3: Run semantic preflight over the final branch**

Run:

```bash
dashi-agda-preflight --root . --errors-only
```

Expected: zero semantic-preflight errors in the new/modified NS canonical modules. Record warnings separately if present.

- [ ] **Step 4: Audit authority and safety invariants from source**

Confirm:

```text
canonical root points to NSConcreteLiteralClayABCDRunTargetExact
NSClayLiteralABCDExact has no Round523 import
new safe owners have zero Round imports
no new owner contains postulate, {!!}, or --allow-unsolved-metas
unsafe bridges are not imported into safe owners
UNRESOLVED rows are not counted as discharged
negative/no-go rows remain present
clayNavierStokesPromoted = false
clayPromotion = false
```

- [ ] **Step 5: Produce the final classification summary**

Report package counts by disposition and explicitly separate:

```text
genuine open obligations
unresolved packages
canonical/superseded/compiler-covered packages
negative/provenance/status packages
```

Do not use a compressed “2,236 -> N” claim unless unresolved count is zero.

- [ ] **Step 6: Commit any final generated-receipt refresh**

```bash
git add .dashi/round-stranded/ns-packages.jsonl
git commit -m "data(ns): refresh canonical extraction receipts"
```

Skip this commit if the artifact is unchanged.

- [ ] **Step 7: Push and open/update the PR against `master`**

PR description must include:

```text
base/head SHA
Tranche A-D summary
classification counts and unresolved count
new canonical owners selected from evidence
unsafe/postulated boundary notes
pytest/preflight commands actually run and their real results
explicit false Clay gates
```

Do not claim Agda kernel/typecheck success unless an Agda build was actually run.

---

## Execution Order and Stop Conditions

Execute Tasks 1–4 first. **Task 4 is a hard evidence gate.** Do not implement Task 5 until the generated full-index receipts have been reviewed and the exact surviving owner set is known.

Stop and return for design/plan revision instead of guessing if any of these occur:

- the concrete canonical run-target authority closure still necessarily depends on a Round theorem owner after Task 1;
- shared-engine factoring changes existing YM package IDs/dispositions beyond the approved additive receipt fields;
- full-domain NS discovery reveals another prefix containing material NS Round lineages outside the two approved prefixes;
- a proposed canonical owner requires a hidden postulate/unsafe dependency that cannot be isolated behind a bridge;
- classification evidence cannot distinguish a proposed `GENUINE_OPEN_OBLIGATION` from `UNRESOLVED` without manual/source research;
- the surviving residual topology no longer fits one terminal scheduler without collapsing distinct theorem/semantic roles.

## Completion Definition

The tranche is ready for review only when:

- authority-root hygiene is complete;
- full NS packages are generated from the current index;
- every package has an evidence-backed disposition or explicit `UNRESOLVED` state;
- every promoted live obligation has exactly one non-Round canonical owner;
- the terminal scheduler contains only those evidence-backed residual owners;
- typed and JSONL receipts preserve negative/unresolved semantics;
- YM regression behavior remains compatible;
- all promotion gates remain false;
- verification results are reported exactly as observed.
