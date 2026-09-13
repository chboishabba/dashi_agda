# Continuous Oscillator Identifiability Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Extend the synthetic continuous-oscillator producer from fixed-frequency reconstruction to a learnable-frequency, query-indexed identifiability experiment without promoting synthetic recovery into neuroscience, 3/6/9 superiority, or mechanism identity.

**Architecture:** Reuse the PR #909 numerical carrier and the merged PR #896 hidden/public refinement. Treat identifiability as consumer/query-relative factorability through the observation projection, with numerical near-collisions as diagnostics only. Preserve Fly/Grokking freeze/held-out discipline, eligible-only MDL/Pareto ordering, and repository snowball attribution/provenance invariants.

**Tech Stack:** Python 3, NumPy, pytest, Agda, existing DASHI `QueryIndexedProjectionAdequacyExact`, `IntersectionalNonFactorability`, `AttributedSourceCore`, `SnowballAttributionProvenanceInvariantExact`.

**Spec:** `docs/superpowers/specs/2026-09-13-continuous-oscillator-identifiability-design.md`

## Global Constraints

- Synthetic/falsifiable first; no biological or Levin interpretation in this tranche.
- Parent chain is retained explicitly: merged PR #896 structural carrier -> PR #909 fixed-frequency producer -> this identifiability tranche.
- `N in {3,6,9}` remains an experimental condition, never an assumed ordering.
- Continuous phase remains distinct from finite `Phase3`; no quantum/Hilbert promotion.
- Waveform adequacy, frequency adequacy, amplitude adequacy, phase adequacy, and hidden-state adequacy are separate queries.
- Numerical near-collision is not an Agda proof of exact non-factorability.
- Gauge/equivalence rules and tolerances are frozen before held-out evaluation.
- Held-out outcomes may not tune selection, thresholds, matching, optimizer budget, or null definitions.
- Optimizer failure is `optimizationUnresolved`, not mathematical non-identifiability.
- Citation/source identity imports neither proof nor authority.
- Snowball retains author/title/publication/DOI-or-explicit-no-DOI/URL/source-kind/formalisation-role/visibility plus proof/authority non-promotion.
- External QID/OEIS/Dewey coordinates are added only when same-object/role-relevant; shared 3/6/9 numerals do not create semantic identity.
- No Agda/kernel GREEN is claimed without an actual execution receipt.

---

### Task 1: RED contract for query-indexed identifiability runtime

**Files:**
- Create: `tests/test_continuous_oscillator_identifiability.py`
- Later create: `scripts/run_continuous_oscillator_identifiability.py`

**Interfaces:**
- Consumes: target constants and numerical conventions from `scripts/run_continuous_oscillator_synthetic.py`.
- Produces: deterministic JSON/CSV receipt schema with query family, frozen design, train/held-out metrics, recovery diagnostics, and promotion flags.

- [ ] Write a focused pytest that invokes the missing identifiability runtime and requires `N={3,6,9}`, learnable frequencies, a train/held-out split, explicit query names, frozen tolerances, and all promotion flags false.
- [ ] Run the focused test and record RED because the runtime does not exist.
- [ ] Commit the RED contract before production implementation.

### Task 2: GREEN minimal learnable-frequency producer

**Files:**
- Create: `scripts/run_continuous_oscillator_identifiability.py`
- Modify only if reuse requires it: `scripts/run_continuous_oscillator_synthetic.py`

**Interfaces:**
- Consumes: target waveform, oscillator-count conditions, deterministic seed conventions.
- Produces: bounded-frequency optimization over amplitudes, phases, and frequencies; training and held-out waveform reconstruction metrics.

- [ ] Implement the smallest bounded-frequency optimizer satisfying Task 1.
- [ ] Keep frequency bounds explicit and deterministic.
- [ ] Preserve the same target support across 3/6/9; redundancy must not silently add target frequencies.
- [ ] Run focused pytest and record GREEN.
- [ ] Commit.

### Task 3: RED/GREEN gauge-aware recovery and near-collision diagnostics

**Files:**
- Modify: `tests/test_continuous_oscillator_identifiability.py`
- Modify: `scripts/run_continuous_oscillator_identifiability.py`

**Interfaces:**
- Produces: phase wrapping, permutation/matching normalization, frequency/amplitude/phase recovery errors, restart basin signatures, observable-distance and parameter-distance pairs.

- [ ] Add failing tests requiring gauge-normalized matching and recovery metrics.
- [ ] Add a failing test that equivalent permutation/phase-wrap representations do not count as distinct hidden states.
- [ ] Add a failing test requiring a near-collision diagnostic: low observable distance with materially larger canonical parameter distance.
- [ ] Implement minimal canonicalization/matching and diagnostics.
- [ ] Keep the receipt language `near_collision_diagnostic`; do not label it an exact non-factorability theorem.
- [ ] Run tests GREEN and commit.

### Task 4: Freeze/held-out and spectral-transfer discipline

**Files:**
- Modify: `tests/test_continuous_oscillator_identifiability.py`
- Modify: `scripts/run_continuous_oscillator_identifiability.py`

**Interfaces:**
- Produces: design-window fit, held-out-time evaluation, unseen spectral-separation evaluation, frozen-rule receipt.

- [ ] Add RED tests requiring the frozen rule to be serialized before held-out metrics.
- [ ] Require held-out time and held-out spectral geometry to be separate coordinates.
- [ ] Require optimizer/matching/tolerance configuration to remain identical across held-out evaluation.
- [ ] Implement minimal split/transfer surfaces and rerun GREEN.
- [ ] Commit.

### Task 5: Null/falsification ladder and conservative classification

**Files:**
- Modify: `tests/test_continuous_oscillator_identifiability.py`
- Modify: `scripts/run_continuous_oscillator_identifiability.py`

**Interfaces:**
- Produces: restart multiplicity, frequency-separation stress, noise ladder, gauge null, spectral-transfer results; class in `{locallyIdentifiable, practicallyIdentifiable, weaklyIdentifiable, nonIdentifiable, optimizationUnresolved}` only when its evidence gate is paid.

- [ ] Add RED tests for restart, noise, separation, gauge, and transfer coordinates.
- [ ] Require refitting/re-optimization where the null changes the fitting problem; never reuse an observed fit as a null result.
- [ ] Implement the minimal bounded null ladder.
- [ ] Require unresolved optimization to remain distinct from non-identifiability.
- [ ] Run GREEN and commit.

### Task 6: Formal query-indexed adapter and attribution snowball

**Files:**
- Create: `DASHI/Cognition/PNF/ContinuousOscillatorIdentifiabilityReceipt.agda`
- Create: `DASHI/Cognition/PNF/ContinuousOscillatorIdentifiabilityRegression.agda`
- Modify narrowly: `DASHI/Cognition/PNF/PNFIRLearningEverything.agda`

**Interfaces:**
- Consumes: `DASHI.Core.QueryIndexedProjectionAdequacyExact`, `DASHI.Core.IntersectionalNonFactorability`, PR #896 oscillator refinement, PR #909 synthetic receipt, `DASHI.Core.AttributedSourceCore`, `DASHI.Core.SnowballAttributionProvenanceInvariantExact`.
- Produces: distinct query constructors for waveform/frequency/amplitude/phase/hidden state; exact finite factorability/non-factorability witness shapes where constructively available; explicit numerical-receipt boundary.

- [ ] Add regression requirements first and establish structural RED by exact branch lookup before creating the owner.
- [ ] Implement query-indexed adapter without a parallel factorisation calculus.
- [ ] Add parent-chain provenance receipt naming PR #896 and PR #909 as implementation lineage, not scientific authority.
- [ ] Add source-role snowball receipts for external scientific precedents actually used by the owner; retain DOI/URL/source role and non-promotion.
- [ ] Keep QID/OEIS/Dewey optional and same-object gated; do not invent identifiers for the synthetic experiment.
- [ ] Wire the narrow aggregate import.
- [ ] Obtain Agda GREEN only from an actual compiler/workflow receipt; otherwise leave certification unpaid.

### Task 7: Roadmap reconciliation with the full thread

**Files:**
- Modify: `Docs/roadmaps/ContinuousOscillatorSyntheticRoadmap.md`
- Modify if needed: `docs/superpowers/specs/2026-09-13-continuous-oscillator-identifiability-design.md`

**Interfaces:**
- Produces: canonical parent-following roadmap rather than a local next-step list.

- [ ] Record the full chain: structural hidden refinement/recursive scale transition -> fixed-frequency falsifiable producer -> query-indexed identifiability -> update-law discrimination -> Lyapunov/stability -> eligible-only MDL/Pareto -> explicit MemoryFibre quotient -> empirical neural/Levin adapters.
- [ ] Retain the earlier thread goals: stable classes broader than minima; environment/history explicit; no universal `F`; present-time target/reference does not imply retrocausation; continuous phase is not `Phase3`; objective/update/measurement stay distinct.
- [ ] Record the still-deferred CRT-on-continuous-carrier lane separately; do not smuggle it into identifiability.
- [ ] Make certification debt orthogonal to scientific roadmap progress: source implementation may advance while kernel status remains unpaid, but no proof promotion occurs.
- [ ] Commit roadmap reconciliation.

### Task 8: Verification wall

- [ ] Run `pytest -q tests/test_continuous_oscillator_synthetic.py tests/test_continuous_oscillator_identifiability.py`.
- [ ] Run `python -m py_compile scripts/run_continuous_oscillator_synthetic.py scripts/run_continuous_oscillator_identifiability.py`.
- [ ] Run focused static/source contract if present.
- [ ] Run narrow Agda owner/regression/aggregate checks only where an executable environment exists.
- [ ] Inspect exact branch diff against master and confirm no unrelated ontology growth.
- [ ] Check exact-head workflow runs and record their actual status.
- [ ] Update PR #909 body with the new tranche, TDD receipts, attribution parent chain, numerical observations, and remaining debt without claiming unobserved GREEN.
