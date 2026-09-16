# Navier–Stokes Paper 1 Modern Proof-Spine Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Migrate Paper 1 from the stale `A1-A9` primary narrative to the modern literal periodic proof spine while preserving the older route as explicit historical/provenance material and keeping all proof/certification claims fail-closed.

**Architecture:** The migration is split into paper-facing status, manuscript structure, readiness tooling, and provenance/certification documentation. The modern main theorem is conditional on the live `CommutatorOnlySpacetimeBudget568` producer; exact downstream compilers and same-object welds are shown separately. The old A1-A9 route remains available as `historicalAlternativeRoute` with explicit reasons for supersession or abandonment.

**Tech Stack:** Agda, Markdown, Python publication-readiness scripts, GitHub Actions/pinned Agda validation workflow.

**Spec:** `Docs/papers/specs/NavierStokesModernProofSpineMigration.md`

## Global Constraints

- Preserve all prior theorem/source attribution; earliest theorem-bearing object retains mathematical credit.
- Preserve the old A1-A9 route in explicit provenance; do not silently delete or rewrite history.
- `R568` is the live analytic producer leaf until a stronger same-object producer is actually proved.
- Consumers/compilers such as `R572` and `R503` must not be described as producers.
- Certification must distinguish source-written, validation root, workflow target, and observed commit-specific Agda success.
- No Clay/global-regularity promotion without the terminal producer and certification receipts.
- PR #890's centered/radial-Plücker lower-separation route is retained as a partially successful historical attempt plus negative control; do not present incidence-only geometry as an anti-alignment theorem.
- External published/claimed Clay-level proofs are compared bidirectionally and do not promote internal results by citation alone.

---

### Task 1: Freeze the paper-facing modern status vocabulary

**Files:**
- Modify: `DASHI/Papers/NavierStokes/TheoremInterface.agda`
- Test/validation: existing paper theorem-interface checker or focused Agda root that imports `DASHI.Papers.NavierStokes.TheoremInterface`

**Interfaces:**
- Consumes: modern R568/R572/R503 owners, same-output Gram owners, final false-guard owners, legacy A6-A9 status owners.
- Produces: one canonical paper-facing status record exposing the modern live producer, downstream compiler chain, historical route status, and certification coordinates.

- [ ] **Step 1: Add imports for the modern proof spine while retaining legacy imports**

Add qualified imports for the exact current owners rather than deleting the A6-A9 imports. Use the repository's exact module names for:

```agda
-- live producer
import DASHI.Physics.Closure.<R568 module> as R568
-- direct compiler
import DASHI.Physics.Closure.<R572 module> as R572
-- direct consumer
import DASHI.Physics.Closure.<R503 module> as R503
-- same-output residual carrier/telescope/payment
import DASHI.Physics.Closure.NSTriadKNComparableFixedOutputCarrierRound207Exact as R207
import DASHI.Physics.Closure.NSTriadKNComparableOutputGramTelescopeRound209Exact as R209
import DASHI.Physics.Closure.NSTriadKNComparableOutputResidualPaymentRound211Exact as R211
```

Do not guess module names for R568/R572/R503: search the repo and use the actual paths.

- [ ] **Step 2: Introduce explicit route/status enums or booleans**

Add a paper-facing classification sufficient to represent at least:

```agda
data PaperRouteRole : Set where
  liveProducerRoute historicalAlternativeRoute fallbackRoute negativeControl : PaperRouteRole

data CertificationState : Set where
  sourceWritten validationRootExists workflowTargetsRoot observedKernelReceipt notRecovered : CertificationState
```

If the repository already has an equivalent shared type, reuse it instead of duplicating it.

- [ ] **Step 3: Add modern status fields without removing old receipts**

The canonical status record must expose, in fail-closed form, at least:

```agda
modernLiveProducerRole : PaperRouteRole
modernLiveProducerRoleIsLive : modernLiveProducerRole ≡ liveProducerRoute

sameOutputResidualStillOpen : R211.round211ConcreteSameOutputResidualPaymentConstructed ≡ false

historicalA1A9Role : PaperRouteRole
historicalA1A9RoleIsHistorical : historicalA1A9Role ≡ historicalAlternativeRoute

clayTerminalPromotionStillFalse : ... ≡ false
```

Do not set any `observedKernelReceipt` field true unless an actual commit-specific receipt is retrieved.

- [ ] **Step 4: Rewrite `paperInterfaceStatement` to describe the modern chain**

The statement must include these distinctions in prose:

```text
R568 = live analytic producer leaf;
R572/R503 = downstream compiler/consumer chain;
same-output between-partner residual remains a quantitative producer problem;
A1-A9 = retained historical alternative route;
terminal Clay/global-regularity promotion remains false.
```

- [ ] **Step 5: Run the focused paper-interface validation**

Use the repository's existing pinned Agda command if available. At minimum run the same checker used by the paper theorem-interface workflow/root.

Expected result: the interface typechecks with legacy imports retained and no new promotion flags.

- [ ] **Step 6: Commit**

```bash
git add DASHI/Papers/NavierStokes/TheoremInterface.agda
git commit -m "refactor(ns-paper): expose modern proof spine in theorem interface"
```

---

### Task 2: Preserve the June A1-A9 paper as explicit history before rewriting the live manuscript

**Files:**
- Create: `Docs/papers/archive/Paper1NavierStokesClayDraft-2026-06-A1-A9.md`
- Modify: `Docs/papers/live/Paper1NavierStokesClayDraft.md`

**Interfaces:**
- Consumes: current June manuscript text.
- Produces: immutable historical snapshot plus a modern live manuscript that links back to it.

- [ ] **Step 1: Copy the current live manuscript verbatim into the archive path**

The archive file must preserve the current title, date, theorem statement, A1-A9 architecture, candidate constants, blockers, and caution language exactly except for a short archival header prepended above it:

```markdown
> Historical snapshot preserved during the 2026-09 modern proof-spine migration.
> This file records the earlier A1-A9 ESS/Abel-defect route and is retained for provenance.
> It is not silently promoted into the current preferred proof route.
```

- [ ] **Step 2: Add a migration banner to the live manuscript**

Replace the old live-title/status header with a modern header that states:

```markdown
Status: live analytic manuscript; modern literal-periodic proof spine; non-promoting
Historical route: the June 2026 A1-A9 manuscript is retained verbatim at ...
Live producer: CommutatorOnlySpacetimeBudget568
```

- [ ] **Step 3: Replace the abstract with the modern conditional theorem framing**

The new abstract must say:

```text
The paper constructs an exact finite periodic/signed-commutator reduction and isolates one live spacetime producer interface.
The theorem remains conditional on that producer.
Earlier ESS/Abel-defect and centered/separation routes are retained as historical/fallback/negative-control provenance where appropriate.
No global regularity or Clay resolution is asserted.
```

- [ ] **Step 4: Add a provenance section near the beginning**

Create `## Historical route provenance and supersession` containing a table with at least:

```markdown
| Route | Original purpose | What was proved | Why not current primary route | Current role |
| A1-A9 ESS/Abel | Tail-flux blowup reduction | theorem grammar / downstream closure surfaces | quantitative A1/A3/A4 producer burden remained | historicalAlternativeRoute |
| constant-band localization | pay Gram debt from shell localization | strong two-sided collar | R214 aligned witness shows localization alone insufficient | negativeControl |
| centered/radial-Pluecker separation (#890) | pay same-output Gram debt by pair separation | same-object difference/PSD plumbing, amplitude telescope | observable map is many-to-one; incidence geometry alone cannot force anti-alignment | historical attempt + negativeControl + reusable plumbing |
| generic Schur/Cotlar | positive fallback | valid reducer interfaces | loses signed structure / still needs uniform producer | fallbackRoute |
| direct signed commutator/R568 | preserve signed structure to final spacetime budget | exact downstream compiler chain | live spacetime producer still open | liveProducerRoute |
```

- [ ] **Step 5: Commit the archival snapshot and provenance banner before large manuscript rewrites**

```bash
git add Docs/papers/archive/Paper1NavierStokesClayDraft-2026-06-A1-A9.md Docs/papers/live/Paper1NavierStokesClayDraft.md
git commit -m "docs(ns-paper): preserve A1-A9 route as explicit provenance"
```

---

### Task 3: Rewrite Paper 1 around the modern causal spine

**Files:**
- Modify: `Docs/papers/live/Paper1NavierStokesClayDraft.md`

**Interfaces:**
- Consumes: migrated theorem interface and archived historical route.
- Produces: paper whose section order matches the modern theorem dependencies.

- [ ] **Step 1: Replace the main theorem with a conditional R568 theorem**

State a theorem of the form:

```markdown
> **Theorem 1.1 (conditional periodic regularity reduction).**
> On the exact periodic Galerkin/continuation carrier formalized below, assume the
> cutoff-uniform `CommutatorOnlySpacetimeBudget568` producer. Then the existing
> exact compiler chain R572 -> R503 -> direct-companion/critical-barrier consumer
> yields the stated continuation conclusion. This theorem is conditional until
> the R568 producer is actually constructed and certified.
```

Do not claim that the assumption is proved.

- [ ] **Step 2: Reorder the manuscript to the nine-section structure in the spec**

Use these headings:

```markdown
1. Main result and claim boundary
2. Literal periodic carrier and exact nonlinear object
3. Signed commutator and low-output geometry
4. Partner compression, same-output Gram residual, and negative controls
5. Historical producer searches and provenance
6. Modern weighted/nested commutator carrier
7. Direct companion quotient and same-object remainder genealogy
8. Live spacetime producer and terminal reduction
9. Certification and reproducibility
```

- [ ] **Step 3: Insert the exact same-object remainder genealogy**

Include the identity in a boxed/displayed form:

```text
F_N^(R104) = integral R406 = 4 * integrated C_direct.
```

For each equality name the owner/module in prose and distinguish theorem from compiler.

- [ ] **Step 4: Add the same-output Gram residual subsection**

Include the exact sequence:

```text
R181 partner compression
-> R207 same-output fixed carrier
-> R209 outputwise telescope
-> R211 quantitative residual payment socket.
```

State the current open condition as:

```text
outputSameModeDebtSum <= R_CC
```

and explain R214 as a no-go only for shell-localization-as-payment.

- [ ] **Step 5: Add PR #890 as transparent negative/provenance evidence**

Describe only what the merged PR records:

```text
same-object compressed difference -> PSD carrier closed;
complete-graph/pair-difference plumbing explored;
amplitude telescope exposed a many-to-one observable map;
incidence-only centered/radial geometry cannot by itself force anti-alignment;
no cutoff-uniform PDE estimate was claimed.
```

- [ ] **Step 6: Add the modern R294/R310/R571-R577 section**

Preserve these firewalls:

```text
Fourier-leg swap != kernel y <-> -y without typed transport;
finite LP stencil != selected smooth torus kernel;
homochiral radial difference != heterochiral radial sum;
positive majorization is downstream of signed cancellation.
```

- [ ] **Step 7: Add the certification appendix table**

For every load-bearing owner include columns:

```markdown
| Owner | Role | MathematicalStatus | StatementStatus | Validation root | Workflow target | Observed kernel receipt | Earliest theorem-bearing date/commit |
```

Populate `not recovered` rather than guessing.

- [ ] **Step 8: Run Markdown/readiness checks**

Run existing publication checks and any markdown/link checker already present.

Expected result: no missing historical route link, no terminal promotion, and the paper's blocker text points to the modern live producer rather than A1/A3-A4 alone.

- [ ] **Step 9: Commit**

```bash
git add Docs/papers/live/Paper1NavierStokesClayDraft.md
git commit -m "docs(ns-paper): migrate Paper 1 to modern proof spine"
```

---

### Task 4: Migrate publication readiness and theorem-variable reporting

**Files:**
- Modify: `scripts/check_publication_readiness.py`
- Modify/regenerate: `Docs/papers/generated/core_papers_theorem_var_manifest.md`
- Modify: `Docs/papers/PublicationRoadmap.md`

**Interfaces:**
- Consumes: modern theorem interface and manuscript headings/status terms.
- Produces: readiness output that separates live modern blockers from historical route blockers.

- [ ] **Step 1: Replace the sole A1/A3-A4 Paper 1 blocker entries**

Add separate readiness rows such as:

```python
{
    "name": "ns-r568-live-spacetime-producer",
    "paper": "Paper1 NS",
    "status": "open",
    "role": "liveProducerRoute",
},
{
    "name": "ns-a1-a9-historical-alternative-route",
    "paper": "Paper1 NS",
    "status": "historical",
    "role": "historicalAlternativeRoute",
},
```

Use the script's actual schema; do not invent unsupported keys if the checker uses a fixed record shape.

- [ ] **Step 2: Add readiness assertions for false terminal promotion**

The checker must continue to fail if the paper/interface claims global regularity or Clay promotion without the corresponding formal receipt.

- [ ] **Step 3: Regenerate or update the theorem-variable manifest**

The manifest must list modern live variables/booleans and retain the legacy route under historical labels rather than deleting it.

- [ ] **Step 4: Update `PublicationRoadmap.md`**

Change Paper 1's primary blocker from `A1/A3 + A4` to the modern producer chain, with a clearly separated historical-route subsection.

- [ ] **Step 5: Run readiness checks**

Run:

```bash
python scripts/check_publication_readiness.py
```

plus the repository command that regenerates/verifies `core_papers_theorem_var_manifest.md`.

Expected result: Paper 1 reports modern live blockers and historical blockers separately.

- [ ] **Step 6: Commit**

```bash
git add scripts/check_publication_readiness.py Docs/papers/generated/core_papers_theorem_var_manifest.md Docs/papers/PublicationRoadmap.md
git commit -m "chore(ns-paper): migrate publication readiness to modern spine"
```

---

### Task 5: Add the bidirectional external-proof reconstruction ledger

**Files:**
- Create: `Docs/papers/NavierStokesExternalProofBidirectionalLedger.md`
- Optionally add a typed owner only if the repository already has a generic bidirectional provenance schema that can be reused without inventing a new planner.

**Interfaces:**
- Consumes: exact external proof sources when separately acquired and the internal section-to-owner map.
- Produces: a non-promoting comparison ledger for claimed/published Clay-level proofs.

- [ ] **Step 1: Create the ledger schema**

Use this table:

```markdown
| External source | Exact lemma/theorem | External assumptions | DASHI nearest owner | External -> DASHI | DASHI -> external | Same-object? | Missing coordinate | Certification/source status |
```

- [ ] **Step 2: Add explicit outcome vocabulary**

The ledger must use only:

```text
equivalentConstruction
oneWayFactorization
sameStatementDifferentProducer
analogyOnly
missingAssumption
contradiction
unresolved
```

- [ ] **Step 3: Add source-role firewall text**

State explicitly:

```text
publication/citation imports neither proof nor authority;
DASHI internal earlier construction dates remain provenance coordinates;
external theorem equivalence requires exact assumption/conclusion and same-object transport;
failed reconstruction is retained rather than erased.
```

- [ ] **Step 4: Do not populate specific external proof claims without current source verification**

Any later population task must retrieve the actual source and publication metadata first.

- [ ] **Step 5: Commit**

```bash
git add Docs/papers/NavierStokesExternalProofBidirectionalLedger.md
git commit -m "docs(ns): add bidirectional external-proof reconstruction ledger"
```

---

### Task 6: Certification-map pass for the proof-critical ancestry

**Files:**
- Create or update the canonical NS portion of: `DASHI/Interop/CrossLaneProofArchaeologyLedgerExact.agda`
- Create/update a human-readable companion only if one already exists; do not create a second canonical ledger.

**Interfaces:**
- Consumes: R101-R132 validation roots; R133-R178 theorem owners; R179-R214 Gram/partner owners; dedicated NS workflow; commit/PR/workflow evidence.
- Produces: one canonical status map used by Paper 1 section 9.

- [ ] **Step 1: Audit only the proof-critical ancestry**

Required slices:

```text
R101-R132
R133-R178
R179-R214
later owners that reach R568/R572/R503
```

Do not mechanically inventory every unrelated NS round.

- [ ] **Step 2: Record the four status coordinates per owner**

For each critical owner store or document:

```text
role
MathematicalStatus
StatementStatus
CertificationStatus
```

plus earliest theorem-bearing commit/date where recoverable.

- [ ] **Step 3: Treat workflow wiring and success receipts separately**

For R185/R193/R200-era roots distinguish:

```text
validation root exists = yes/no
workflow invokes root = yes/no
observed head-specific successful Agda run = exact receipt or notRecovered
```

- [ ] **Step 4: Preserve abandoned route history**

Add provenance rows for:
- A1-A9;
- shell-localization/no-go;
- centered/radial separation PR #890;
- Schur/Cotlar fallback;
- direct signed/R568 live route.

- [ ] **Step 5: Commit**

```bash
git add DASHI/Interop/CrossLaneProofArchaeologyLedgerExact.agda
git commit -m "docs(ns): freeze proof-critical archaeology and certification map"
```

---

### Task 7: Final consistency verification

**Files:**
- No new production files unless a verification failure requires a targeted correction.

**Interfaces:**
- Consumes: Tasks 1-6.
- Produces: evidence that manuscript, interface, readiness, provenance, and certification surfaces agree.

- [ ] **Step 1: Run the focused Agda validation for `TheoremInterface.agda`**

Use the repository's pinned Agda wrapper/checker.

Expected: success, or record the exact failure without promoting certification.

- [ ] **Step 2: Run publication readiness**

```bash
python scripts/check_publication_readiness.py
```

Expected: success with modern/historical route separation.

- [ ] **Step 3: Run generated-manifest consistency check**

Use the existing generation/check command.

Expected: no diff after regeneration.

- [ ] **Step 4: Search for stale headline blocker language**

Search Paper 1-facing files for phrases that still make `A1/A3` or `A4` the sole current blocker.

Expected: occurrences are confined to archived/historical route discussion.

- [ ] **Step 5: Search for accidental promotion language**

Search for:

```text
Clay solved
global regularity proved
R568 proved
kernel checked
```

Review every hit manually. Historical quotation is allowed; current unsupported promotion is not.

- [ ] **Step 6: Commit any consistency fixes**

```bash
git add <only files changed by verification fixes>
git commit -m "fix(ns-paper): align manuscript interface and readiness status"
```

## Self-review

- Spec coverage: manuscript migration, historical provenance, theorem-interface migration, publication readiness, certification map, and bidirectional external-proof reconstruction are each assigned to explicit tasks.
- Placeholder scan: no implementation task relies on `TBD`/`TODO`; where exact module names are not yet known, the task explicitly requires repository search before editing rather than guessing.
- Type consistency: route/certification vocabulary is introduced in Task 1 and reused in later tasks; if an existing shared type is found, all later uses must adopt that existing type instead.

## Execution order

Recommended order:

```text
Task 1 -> Task 2 -> Task 3 -> Task 4 -> Task 6 -> Task 7
                    \-> Task 5 can proceed independently after the schema is fixed.
```

The proof-construction lane itself should remain separate from this publication migration. New PDE work should continue forward from named unpaid fields rather than reopening broad archaeology.
