# YM + Unification Full Proof Spines Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Convert the live Paper 3 Yang–Mills and Paper 8 unification manuscripts from status/Boolean closure surfaces into typed, compositional proof spines whose open analytic inputs are explicit theorem fields and whose downstream consumers are compiler-owned.

**Architecture:** Keep the two manuscripts separate at their true analytic walls. Paper 3 gets a typed H3a → H3b → no-spectral-pollution → OS/Wightman → positive-gap spine, reusing existing authority/closure owners without promoting missing inputs. Paper 8 gets a typed UCT.1 → UCT.2 → UCT.3 → UCT.4 package feeding the already-existing modulo-null/Jordan-von-Neumann consumers. Cross-lane unification occurs only through shared closure grammar and typed downstream consumers, never by using Paper 8 to manufacture Paper 3 analytic inputs.

**Tech Stack:** Agda 2.9 safe modules, existing DASHI `ProofLevel` discipline, GitHub branch `agent/cross-lane-proof-archaeology-ledger`, focused shell validation roots.

**Spec:** `Docs/papers/live/Paper3YangMillsClayDraft.md`, `Docs/papers/live/Paper8UnificationDraft.md`, `Docs/support/reference/YMRHPRRoundArchaeologyAudit.md`

## Global Constraints

- Preserve source/proof/status separation: citation or `standardImported` metadata does not inhabit theorem fields.
- Preserve fail-closed semantics: no Clay, terminal-unification, OS, Wightman, H3a, H3b, no-pollution, or UCT promotion without a theorem-bearing witness.
- Reuse existing owners before introducing new mathematical abstractions.
- Keep Paper 3 and Paper 8 analytic walls separate; Paper 8 is not a substitute for YM continuum analysis.
- Validation claims require exact-head Agda/kernel receipts; static source edits alone are not called verified.
- Primary source coordinates remain attached to their existing owners; do not invent DOI/QID/Dewey/OEIS identifiers.

---

### Task 1: Paper 3 typed continuum-transfer proof spine

**Files:**
- Create: `DASHI/Physics/Closure/YMPaper3ContinuumTransferProofSpineExact.agda`
- Test: `DASHI/Physics/Closure/YMPaper3ContinuumTransferProofSpineValidation.agda`
- Test script: `scripts/check_ym_paper3_continuum_transfer_spine.sh`

**Interfaces:**
- Consumes: existing finite-gap surfaces, `YMContinuumMassGapTransferAuthority`, OS/Wightman authority owners, and current H3a/H3b/no-pollution boundary owners.
- Produces: theorem-bearing records `H3aTransferTheorem`, `H3bVacuumProjectionTheorem`, `NoSpectralPollutionTheorem`, and `Paper3ContinuumTransferSpine`, plus a compiler from those witnesses to the existing continuum-transfer consumer.

- [ ] **Step 1: Write the failing validation root**

Create a validation module importing the intended proof-spine module and asserting that the three analytic theorem fields are explicit inputs rather than Booleans generated locally.

- [ ] **Step 2: Verify RED**

Run `AGDA_JOBS=1 bash scripts/check_ym_paper3_continuum_transfer_spine.sh`.
Expected: FAIL because `YMPaper3ContinuumTransferProofSpineExact.agda` does not yet exist.

- [ ] **Step 3: Implement the minimal typed spine**

Define records whose fields are propositions/functions over abstract operator/vacuum/gap carriers. Do not postulate or manufacture inhabitants. Add only compiler functions that compose supplied witnesses into downstream existing authority/consumer records.

- [ ] **Step 4: Verify GREEN when Agda is available**

Run the focused checker. Expected: PASS with no holes/postulates/unsafe escapes in the new modules. If Agda is unavailable, record that exact validation boundary without claiming success.

- [ ] **Step 5: Commit**

Commit the spine, validator, and checker together.

### Task 2: Paper 8 typed UCT.1–UCT.4 proof spine

**Files:**
- Create: `DASHI/Physics/Closure/UnificationUCTFullProofSpineExact.agda`
- Test: `DASHI/Physics/Closure/UnificationUCTFullProofSpineValidation.agda`
- Test script: `scripts/check_unification_uct_full_proof_spine.sh`

**Interfaces:**
- Consumes: `UnificationCrossTermNullityTheoremBoundary`, `UCTPromotionEvidenceResidualBoundary`, null-class stability, null-to-quotient transport, modulo-null linearity, four-point, parallelogram, and JvN adapter owners.
- Produces: `UCT1ResidualPDE`, `UCT2OperatorClass`, `UCT3UniqueContinuation`, `UCT4CrossTermNullity`, aggregate `UCTAnalyticPackage`, and compiler into the existing UCT.4 theorem target/downstream consumers.

- [ ] **Step 1: Write the failing validation root**

Validation must require UCT.1–UCT.4 as theorem-bearing fields and ensure UCT.5–UCT.8 are downstream compiler outputs only.

- [ ] **Step 2: Verify RED**

Run `AGDA_JOBS=1 bash scripts/check_unification_uct_full_proof_spine.sh`.
Expected: FAIL because `UnificationUCTFullProofSpineExact.agda` does not yet exist.

- [ ] **Step 3: Implement the minimal typed UCT spine**

Represent the residual PDE, operator-class witness, unique-continuation theorem, and cross-term-nullity result as dependent records tied to the exact `actualU1aCrossTerm` carrier. No strings or Boolean status flags may serve as proof fields.

- [ ] **Step 4: Compile UCT.4 into existing consumers**

Add only the adapters justified by existing null-class stability and quotient-transport owners. Do not promote JvN or terminal unification unless the existing typed consumers accept the UCT.4 witness directly.

- [ ] **Step 5: Verify GREEN when Agda is available and commit**

Run the focused checker and commit the proof spine if validation passes; otherwise retain the source with an explicit unverified status only if static audit shows no invented proof.

### Task 3: Replace Paper-3 Boolean transfer intake with typed adapters

**Files:**
- Modify: `DASHI/Physics/Closure/YMContinuumMassGapTransferAuthority.agda`
- Modify validation from Task 1.

**Interfaces:**
- Consumes: `Paper3ContinuumTransferSpine`.
- Produces: a typed adapter into `ContinuumMassGapTransferProvider`; existing Boolean authority compatibility remains legacy metadata only.

- [ ] **Step 1:** Add a failing validation requiring the typed adapter.
- [ ] **Step 2:** Add the adapter without deleting legacy API.
- [ ] **Step 3:** Prove by construction that no typed provider can be obtained without H3a/H3b/no-pollution inputs.
- [ ] **Step 4:** Run focused validation and commit.

### Task 4: Connect Paper-8 UCT.4 to U-1a/JvN consumer chain

**Files:**
- Modify: `DASHI/Physics/Closure/UnificationCrossTermNullityTheoremBoundary.agda` only if needed.
- Modify validation from Task 2.

**Interfaces:**
- Consumes: `UCT4CrossTermNullity` plus existing representative invariance/null stability data.
- Produces: existing modulo-null linearity input, then existing four-point/parallelogram/JvN consumer chain.

- [ ] **Step 1:** Identify the exact existing consumer type that first accepts cross-term nullity.
- [ ] **Step 2:** Add the smallest adapter from the typed UCT.4 witness.
- [ ] **Step 3:** Keep UCT.5–UCT.8 compiler-only; do not duplicate their mathematics.
- [ ] **Step 4:** Run focused validation and commit.

### Task 5: Paper-to-proof traceability map

**Files:**
- Create: `Docs/support/reference/YMUnificationPaperToProofMap.md`
- Modify: `Docs/papers/live/Paper3YangMillsClayDraft.md` only to add formal-owner links/status if necessary.
- Modify: `Docs/papers/live/Paper8UnificationDraft.md` only to add formal-owner links/status if necessary.

**Interfaces:**
- Consumes: Tasks 1–4 exact theorem names.
- Produces: manuscript theorem/section → Agda owner → proof status → remaining analytic input mapping.

- [ ] **Step 1:** Map Paper 3 Theorems 1.1, 5.1, 5.2 and H3a/H3b/no-pollution to exact owners.
- [ ] **Step 2:** Map Paper 8 U-1a, U-1a-H, UCT.1–UCT.8 to exact owners.
- [ ] **Step 3:** Mark every item as compiler-owned, theorem-bearing, imported authority, or open analytic input.
- [ ] **Step 4:** Link the map from PR #883 and commit.

### Task 6: Full-proof next analytic cut

**Files:** determined by Tasks 1–5; no new planner.

**Interfaces:**
- Consumes: exact open theorem fields exposed by typed proof spines.
- Produces: the first actual mathematical proof decrement.

- [ ] **Step 1:** Pareto-rank open Paper-3 and Paper-8 theorem fields by dependency impact and available in-repo donors.
- [ ] **Step 2:** Choose one non-dominated field only.
- [ ] **Step 3:** Search same-object repo donors and primary-source owners.
- [ ] **Step 4:** Implement the smallest theorem-bearing decrement with a focused failing/passing validator.
- [ ] **Step 5:** Update the paper-to-proof map and archaeology audit.
