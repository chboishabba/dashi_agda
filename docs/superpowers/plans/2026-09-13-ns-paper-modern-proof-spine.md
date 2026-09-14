# Navier–Stokes Paper 1 Modern Proof-Spine Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Replace Paper 1’s stale June A1–A9 primary narrative and canonical paper theorem interface with the modern R104/R406 → `C_direct` → R568 → R572 → R503 causal proof spine, while preserving A1–A9 and Round62-era work honestly as historical/alternative provenance and keeping all open analytic producers fail-closed.

**Architecture:** Update the canonical manuscript and canonical `DASHI.Papers.NavierStokes.TheoremInterface` in place. Reuse existing theorem owners and historical round interfaces rather than creating a parallel paper API; add only a focused validation root/status contract needed to make the migrated interface kernel-checkable. Synchronize publication/analytic-status documents so they all name the same live cutset and status axes.

**Tech Stack:** Agda 2.9 pinned repo checker (`scripts/run_agda29_parallel_check.sh`), Markdown paper/docs, existing GitHub Actions NS focused workflow, source-level grep/anti-hole checks.

**Spec:** `docs/superpowers/specs/2026-09-13-ns-paper-modern-proof-spine-design.md`

## Global Constraints

- Do not create a second live NS manuscript or a second canonical theorem interface.
- Preserve the June A1–A9 route as explicit historical/alternative provenance; do not delete, sanitize, or retroactively rewrite it.
- `C_direct` is constructed. Never describe it as the missing object.
- R568 / `CommutatorOnlySpacetimeBudget568` is the live analytic producer leaf unless a genuinely source-written producer closes it during implementation.
- R572 is a compiler from R568 to the existing direct leaf-A consumer surface; do not classify it as an independent PDE producer.
- R503 is the direct downstream budget/consumer surface, not the R568 producer.
- P3 / same-output between-partner debt is the current local proof-search frontier and remains open unless proof state changes independently.
- Keep `MathematicalStatus`, `StatementStatus`, and `CertificationStatus` separate.
- `CertificationStatus` must separately record validation-root existence, workflow targeting, and observed commit-specific Agda success receipt.
- Workflow configuration alone is not a kernel receipt.
- Do not promote Clay/global regularity while P3/R568 or downstream required producers remain open.
- Retain negative controls/superseded routes, especially R214 constant-band Gram no-go and positive-majorant fallback routes.

---

### Task 1: Add a fail-closed migration contract before changing paper-facing surfaces

**Files:**
- Create: `scripts/check_ns_paper_modern_proof_spine.py`
- Modify later in this task only if an existing publication-readiness aggregator is discovered: the exact aggregator that already executes Paper 1 source checks.

**Interfaces:**
- Consumes: current `Docs/papers/live/Paper1NavierStokesClayDraft.md`; current `DASHI/Papers/NavierStokes/TheoremInterface.agda`; existing modern owners R568/R572/R503/R414/R500/R507 and same-output owners R207/R209/R211/R214.
- Produces: one deterministic source-level contract that fails while the canonical paper/interface are stale and passes only when the modern owner chain, historical A1–A9 provenance, open P3/R568 guards, and three-axis status language are all present.

- [ ] **Step 1: Write the failing checker.**

Implement `scripts/check_ns_paper_modern_proof_spine.py` so it reads the two primary files and requires all of the following literal surfaces:

```python
REQUIRED_PAPER = [
    "CommutatorOnlySpacetimeBudget568",
    "R568",
    "R572",
    "R503",
    "C_direct",
    "same-output",
    "P3",
    "MathematicalStatus",
    "StatementStatus",
    "CertificationStatus",
    "historical/alternative",
    "A1-A9",
    "R214",
]

REQUIRED_INTERFACE = [
    "CommutatorOnlySpacetimeBudget568",
    "directCompanionConstructed",
    "commutatorOnlySpacetimeProducerClosed",
    "directLeafACompilerConstructed",
    "directOffDiagonalConsumerConstructed",
    "sameOutputDebtPaymentClosed",
    "p3SeparationProducerClosed",
    "historicalAlternativeRoute",
    "clayTerminalPromotion",
]

FORBIDDEN_PRIMARY_PAPER_PHRASES = [
    "Its live frontiers are the quantitative `A1/A3`",
    "The current Clay-blocking frontier is also sharp. The coupled `A1/A3` problem",
]
```

The checker must fail if any required token is missing, if any forbidden stale-primary phrase remains outside the historical appendix section, or if the migrated interface sets the R568/P3/Clay terminal guards to `true`.

- [ ] **Step 2: Run the checker and record RED.**

Run:

```bash
python scripts/check_ns_paper_modern_proof_spine.py
```

Expected: FAIL because the current manuscript and canonical interface are still A1–A9/Round62-primary.

- [ ] **Step 3: Commit the RED contract.**

```bash
git add scripts/check_ns_paper_modern_proof_spine.py
git commit -m "test: pin modern NS paper proof-spine migration contract"
```

---

### Task 2: Replace the canonical theorem interface in place with the modern fail-closed spine

**Files:**
- Modify: `DASHI/Papers/NavierStokes/TheoremInterface.agda`
- Read/reuse, do not replace: `DASHI/Papers/NavierStokes/TheoremInterfaceRound*.agda`
- Test: `scripts/check_ns_paper_modern_proof_spine.py`

**Interfaces:**
- Consumes exact owners:
  - `DASHI.Physics.Closure.NSTriadKNLiveCommutatorOnlyLeafABoundaryRound568Exact` / `CommutatorOnlySpacetimeBudget568`.
  - `DASHI.Physics.Closure.NSTriadKNDirectLeafACompilerRound572Exact`.
  - `DASHI.Physics.Closure.NSTriadKNDirectResolventSignedCrossToR415Round503Exact`.
  - `DASHI.Physics.Closure.NSTriadKNDirectResolventIntegratedCompanionRound500Exact`.
  - `DASHI.Physics.Closure.NSTriadKNOneCancellationPaysRemainderAndCriticalRound414Exact`.
  - `DASHI.Physics.Closure.NSTriadKNRound104ToLiteralR406CriticalSliceRound507Exact`.
  - same-output debt owners R207/R209/R211 and negative control R214.
  - historical A6–A9/Clay23/Final owners already imported by the old interface.
- Produces canonical paper-facing status fields for the modern chain while retaining historical A1–A9 metadata.

- [ ] **Step 1: Resolve exact imported theorem/status symbol names before editing.**

Use repo search/fetch to identify the exact Boolean/status symbols proving or recording:

```text
R568 producer status/open flag
R572 compiler constructed status
R503 direct-off-diagonal budget/consumer status
R500 direct companion construction
R414/R507 same-object remainder lineage
R207/R209/R211 same-output debt/payment status
R214 localization-no-go status
```

Do not invent symbol names. Record the resolved names in comments next to imports if needed.

- [ ] **Step 2: Rewrite imports around the modern chain while preserving historical imports needed for provenance.**

The canonical file should import modern owners explicitly and retain only the old A6–A9/Clay/Final imports needed to expose the historical route and terminal false guards. Do not delete the separate `TheoremInterfaceRound*.agda` files.

- [ ] **Step 3: Replace the old `NSPaperTheoremStatus` primary fields with three grouped status families.**

Use one canonical record with these paper-facing names:

```agda
record NSPaperTheoremStatus : Setω where
  field
    -- Modern canonical spine
    directCompanionConstructed : Bool
    commutatorOnlySpacetimeProducerClosed : Bool
    directLeafACompilerConstructed : Bool
    directOffDiagonalConsumerConstructed : Bool

    -- Current proof-search frontier
    sameOutputDebtIdentityConstructed : Bool
    sameOutputDebtPaymentClosed : Bool
    p3SeparationProducerClosed : Bool

    -- Historical provenance
    historicalAlternativeRoute : String
    historicalA1A9Retained : Bool
    historicalRound62Retained : Bool

    -- Claim guard
    clayTerminalPromotion : Bool

    statement : String
```

For every field with an existing authoritative owner, add equality witnesses tying the field to that owner rather than duplicating an optimistic literal. Set P3/R568/Clay terminal promotion fail-closed from their authoritative current status.

- [ ] **Step 4: Make the canonical statement explicit and non-promoting.**

`paperInterfaceStatement` must say, in substance and owner language:

```text
C_direct is constructed; R568 is the live cutoff-uniform commutator-only spacetime producer; R572 compiles a paid R568 budget into the existing direct leaf-A/direct-off-diagonal consumer; P3/same-output debt payment remains an open local producer; A1-A9 and Round62 are retained as historical/alternative routes; no unconditional Clay/global-regularity promotion is made.
```

- [ ] **Step 5: Run source contract.**

```bash
python scripts/check_ns_paper_modern_proof_spine.py
```

Expected: interface-related checks pass; manuscript-related checks remain RED until Task 3.

- [ ] **Step 6: Commit theorem-interface migration.**

```bash
git add DASHI/Papers/NavierStokes/TheoremInterface.agda
git commit -m "refactor: migrate NS paper interface to modern proof spine"
```

---

### Task 3: Rewrite Paper 1 around the causal proof spine and preserve A1–A9 as historical provenance

**Files:**
- Modify: `Docs/papers/live/Paper1NavierStokesClayDraft.md`
- Test: `scripts/check_ns_paper_modern_proof_spine.py`

**Interfaces:**
- Consumes: canonical theorem interface from Task 2 and the exact owner map in the design spec.
- Produces: one live manuscript whose primary sections follow the modern causal chain; the old June route survives as a clearly dated historical/alternative appendix.

- [ ] **Step 1: Replace title/front matter/abstract.**

Use a title such as:

```markdown
# Paper 1 Draft: Navier–Stokes Signed-Commutator Reduction and Direct-Companion Frontier
```

Keep original author/date provenance visible, add a migration revision date `2026-09-13`, and state that the current result remains conditional on the open R568 producer. The abstract must distinguish constructed compiler/same-object infrastructure from the open analytic producer.

- [ ] **Step 2: Replace the main theorem section with the modern conditional theorem.**

The main statement must be conditional on an inhabitant of `CommutatorOnlySpacetimeBudget568`; it must say the downstream R572→R503→critical-barrier chain is constructed. It must not claim that R568 itself has been proved.

- [ ] **Step 3: Add the literal periodic/helical carrier section.**

Describe only theorem-relevant finite periodic Fourier/Leray/helical/physical-incidence structure. Explicitly separate exact finite algebra from standard/imported continuum authority.

- [ ] **Step 4: Add signed commutator/helical construction section.**

Map the narrative to R571 plus R573/R574 neighbors, and retain July signed multiplier-difference, early-August centered moment, six-three, R127/R128, and R172–R178 as historical donors rather than modern claims.

- [ ] **Step 5: Add same-output Gram/covariance and P3 sections.**

State the exact historical chain R179/R180/R181/R201/R205–R214, with R207 same-output restriction, R209 outputwise debt telescope, and R211 payment socket. State explicitly that R214 proves constant shell width alone cannot pay the debt. Describe PR #890 only as active construction unless its proof/certification status changes before merge.

Include the complete-graph identity in the correct polarity:

```text
Debt = (n-1) * sum ||B_alpha||^2
       - sum_{alpha<beta} ||B_alpha - B_beta||^2.
```

State that physical lower control of pairwise separation is the P3 producer problem; do not identify arbitrary inter-partner differences with a single R176 cell.

- [ ] **Step 6: Add weighted/full-square, direct-companion, and terminal compiler sections.**

Make R294→R545→R567→R568 the weighted/full-square route; then expose R414/R500/R503/R507 same-object/direct-companion ancestry. State explicitly:

```text
C_direct constructed != C_direct uniformly paid.
R568 = live producer.
R572 = compiler.
R503 = downstream direct-off-diagonal budget/consumer.
```

Keep R575/R576/R577 nested/positive Gram routes as valid fallback reductions, not the canonical producer by default.

- [ ] **Step 7: Move the old A1–A9 manuscript into a historical/alternative appendix inside the same file.**

Preserve the original June route’s theorem statement, ESS/Abel motivation, unresolved A1/A3 and A4 frontiers, and the reason it ceased to be primary: it no longer matches the shortest modern same-object/direct-companion proof spine. Do not describe it as an error or strawman; label any still-useful diagnostics/donor constructions.

- [ ] **Step 8: Add certification/status appendix.**

Use the table columns:

```markdown
| owner | role | MathematicalStatus | StatementStatus | CertificationStatus |
```

For `CertificationStatus`, use text of the form:

```text
validation root: yes/no; workflow target: yes/no; observed head-specific Agda receipt: yes/no/not recovered
```

Populate proof-critical roots at least for R101–R132 checkpoints, R185, R193, R200–R214, and the later R4xx/R5xx owners actually cited by the paper. Do not infer a successful historical Agda run merely from workflow wiring.

- [ ] **Step 9: Run source contract.**

```bash
python scripts/check_ns_paper_modern_proof_spine.py
```

Expected: PASS for primary manuscript/interface consistency.

- [ ] **Step 10: Commit manuscript migration.**

```bash
git add Docs/papers/live/Paper1NavierStokesClayDraft.md
git commit -m "docs: migrate Paper 1 to modern NS proof spine"
```

---

### Task 4: Synchronize publication and analytic-state reference surfaces

**Files:**
- Modify: `Docs/papers/PublicationRoadmap.md`
- Modify: `Docs/roadmaps/ClayNSProofRoadmap.md`
- Modify: `Docs/support/reference/NSAnalyticState.md`
- Modify: `Docs/support/reference/AgdaValidationTargets.md`
- Modify only if current wording requires it: `Docs/papers/README.md`

**Interfaces:**
- Consumes: migrated manuscript and theorem interface.
- Produces: one consistent public/internal status vocabulary for Paper 1.

- [ ] **Step 1: Replace A1/A3/A4-as-primary wording with the modern cutset in the publication roadmap.**

Required status wording must include `R568 live producer`, `R572 compiler`, `R503 consumer`, `P3 same-output debt frontier`, and `A1-A9 historical/alternative route`.

- [ ] **Step 2: Update the Clay NS roadmap to point at named unpaid fields rather than broad archaeology.**

The immediate proof-search order should be:

```text
P3 fixed-output compressed-partner separation
-> R211 same-output residual payment
-> shortest same-object transplant into modern R568 route
-> R568 spacetime producer
-> R572/R503 downstream compiler chain
```

Retain historical failed/superseded routes and explain why they were abandoned or demoted.

- [ ] **Step 3: Update `NSAnalyticState.md` with the exact modern proof-state snapshot.**

Record at minimum:

```text
C_direct constructed
R568 open live producer
R572 constructed compiler
R503 constructed downstream budget
P3 open
R214 negative control retained
A1-A9 historical alternative retained
```

- [ ] **Step 4: Update `AgdaValidationTargets.md` with certification firewall.**

List the focused validation roots/workflow targets that exist and explicitly distinguish them from observed commit-specific success receipts. Include the new canonical theorem-interface validation root added in Task 5.

- [ ] **Step 5: Run source contract and grep stale primary wording.**

```bash
python scripts/check_ns_paper_modern_proof_spine.py
grep -R "A1/A3.*live\|A4.*live" Docs/papers/PublicationRoadmap.md Docs/roadmaps/ClayNSProofRoadmap.md Docs/support/reference/NSAnalyticState.md
```

Expected: checker PASS; grep returns only clearly historical/alternative references, not primary live-frontier claims.

- [ ] **Step 6: Commit synchronization.**

```bash
git add Docs/papers/PublicationRoadmap.md Docs/roadmaps/ClayNSProofRoadmap.md Docs/support/reference/NSAnalyticState.md Docs/support/reference/AgdaValidationTargets.md Docs/papers/README.md
git commit -m "docs: synchronize modern NS paper status surfaces"
```

---

### Task 5: Add a focused Agda validation root for the migrated canonical theorem interface

**Files:**
- Create: `DASHI/Papers/NavierStokes/TheoremInterfaceValidation.agda`
- Modify: the existing focused NS workflow that invokes `scripts/run_agda29_parallel_check.sh` for proof-frontier roots (currently `.github/workflows/ns-triad-concrete-retained-fiber-agda.yml` if still canonical at execution time).
- Test: `DASHI/Papers/NavierStokes/TheoremInterfaceValidation.agda`

**Interfaces:**
- Consumes: canonical `DASHI.Papers.NavierStokes.TheoremInterface`.
- Produces: a small cumulative validation root that checks the canonical modern paper interface’s closed/open declarations without changing proof content.

- [ ] **Step 1: Write the validation root.**

Import `DASHI.Papers.NavierStokes.TheoremInterface as Paper` and assert by `refl`/authoritative equalities that:

```agda
directCompanionConstructed = true
directLeafACompilerConstructed = true
directOffDiagonalConsumerConstructed = true
sameOutputDebtPaymentClosed = false
p3SeparationProducerClosed = false
commutatorOnlySpacetimeProducerClosed = false
clayTerminalPromotion = false
historicalA1A9Retained = true
```

Use the canonical status record; do not duplicate proof-owner booleans independently.

- [ ] **Step 2: Run the pinned Agda checker locally if available.**

```bash
bash scripts/run_agda29_parallel_check.sh DASHI/Papers/NavierStokes/TheoremInterfaceValidation.agda
```

Expected: PASS. If the environment cannot execute Agda, record verification as inconclusive and do not claim kernel certification.

- [ ] **Step 3: Wire the validation root into the existing focused NS workflow.**

Add a clearly named workflow step:

```yaml
- name: Type-check canonical Paper 1 modern theorem interface
  run: bash scripts/run_agda29_parallel_check.sh DASHI/Papers/NavierStokes/TheoremInterfaceValidation.agda
```

Do not create a second workflow unless the existing one is demonstrably unsuitable.

- [ ] **Step 4: Run YAML/source sanity checks.**

```bash
python - <<'PY'
from pathlib import Path
p = Path('.github/workflows/ns-triad-concrete-retained-fiber-agda.yml')
s = p.read_text()
assert 'TheoremInterfaceValidation.agda' in s
assert 'run_agda29_parallel_check.sh' in s
print('workflow wiring ok')
PY
```

- [ ] **Step 5: Commit validation wiring.**

```bash
git add DASHI/Papers/NavierStokes/TheoremInterfaceValidation.agda .github/workflows/ns-triad-concrete-retained-fiber-agda.yml
git commit -m "ci: type-check canonical modern NS paper interface"
```

---

### Task 6: Run publication/readiness and anti-hole verification without overclaiming certification

**Files:**
- Modify only if required by an existing manifest contract: publication-readiness manifest/test files discovered during execution.
- No theorem/proof code should change in this task.

**Interfaces:**
- Consumes all prior tasks.
- Produces a verification receipt separating source consistency, local Agda outcome, workflow wiring, and observed CI run state.

- [ ] **Step 1: Run source migration checker.**

```bash
python scripts/check_ns_paper_modern_proof_spine.py
```

Expected: PASS.

- [ ] **Step 2: Run existing anti-hole/postulate checks used by the focused NS workflow.**

Read `.github/workflows/ns-triad-concrete-retained-fiber-agda.yml` and run the exact anti-hole/checker commands it uses before Agda. Do not substitute a weaker command.

- [ ] **Step 3: Run focused Agda validation root.**

```bash
bash scripts/run_agda29_parallel_check.sh DASHI/Papers/NavierStokes/TheoremInterfaceValidation.agda
```

Expected: PASS when Agda is available. If unavailable, report `CertificationStatus = workflow-targeted/local-run-unavailable`, not certified.

- [ ] **Step 4: Run repository diff/format sanity.**

```bash
git diff --check
```

Expected: no output.

- [ ] **Step 5: Inspect implementation-head CI state after push.**

Use GitHub commit workflow/status APIs. Record separately:

```text
validation root exists: yes
workflow targets root: yes
observed implementation-head Agda run: success / failure / not observed
```

Do not convert `not observed` into success.

- [ ] **Step 6: Commit only manifest/readiness repairs discovered by verification.**

If none are required, do not make a cosmetic commit.

---

### Task 7: Final self-review against the approved design and publish the migration receipt

**Files:**
- Review all modified files.
- Update the design/plan only if implementation discovered a factual owner-name correction; do not rewrite history to match implementation.

**Interfaces:**
- Consumes complete implementation.
- Produces final branch state ready for review/merge, with explicit open-producer and certification boundaries.

- [ ] **Step 1: Check every design success criterion manually.**

Verify:

```text
1 Paper main narrative = modern spine
2 A1-A9 retained honestly
3 canonical theorem interface = modern and fail-closed
4 C_direct described as constructed
5 R568 producer / R572 compiler / R503 consumer classification correct
6 P3 represented as open local frontier
7 Mathematical/Statement/Certification statuses distinct
8 no unconditional Clay/global-regularity claim
```

- [ ] **Step 2: Search for accidental promotion language.**

```bash
grep -RniE "Clay problem (is|has been) solved|global regularity (is|has been) proved|R568.*closed|P3.*closed" \
  Docs/papers/live/Paper1NavierStokesClayDraft.md \
  DASHI/Papers/NavierStokes/TheoremInterface.agda \
  Docs/papers/PublicationRoadmap.md \
  Docs/roadmaps/ClayNSProofRoadmap.md \
  Docs/support/reference/NSAnalyticState.md
```

Any hit must be inspected; only negated/historical wording is permitted while the authoritative status remains open.

- [ ] **Step 3: Run final verification bundle.**

```bash
python scripts/check_ns_paper_modern_proof_spine.py
git diff --check
bash scripts/run_agda29_parallel_check.sh DASHI/Papers/NavierStokes/TheoremInterfaceValidation.agda
```

If Agda cannot run, omit the success claim and report the exact wall.

- [ ] **Step 4: Commit final factual corrections only if needed.**

```bash
git add <only-files-that-needed-final-correction>
git commit -m "docs: finalize modern NS paper migration receipt"
```

- [ ] **Step 5: Record final receipt.**

Report exact head SHA plus:

```text
source contract: PASS/FAIL
anti-hole checks: PASS/FAIL/not run
local Agda validation: PASS/FAIL/unavailable
workflow target: yes/no
observed head-specific Agda workflow receipt: success/failure/not observed
P3: open/closed
R568: open/closed
Clay terminal promotion: false/true
```
