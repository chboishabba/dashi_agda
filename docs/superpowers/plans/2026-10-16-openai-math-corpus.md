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


## 29 October 2026 — Source-first new proof: unique auxiliary-gate extension

**Existing owners actually inspected (default-branch source, not PR summaries):**
- `DASHI/Mathematics/Complexity/PNotEqualsNPConcreteCircuitSharedSemanticsExact.agda` contains `sharedConstraintsGiveRealization`, `assignmentFromProgram`, `assignmentFromProgramInputCorrect`, `assignmentFromProgramGateCorrect`, `acceptedInputGivesSharedSatisfiable`, `sharedSatisfiableGivesAcceptedInput`.
- `PNotEqualsNPConcreteCircuitSharedCompilerExact.agda` owns gate-index numbering and actual shared/Tseitin formula construction.
- `PNotEqualsNPConcreteCircuitSharedUpperBoundExact.agda` owns linear formula **syntax-node** size bounds. Its upper bound is NOT a bit-encoding bound or TM runtime theorem.
- `PNotEqualsNPConcreteBooleanCircuitDAGExact.agda` owns actual acyclic gates and a finite input vector.
- Prior #1040 (created 2026-09-24, merged by 2026-10-04) retains original DASHI source ownership, before the public OpenAI October 26 ETH release. Historical Cook/Levin and Tseitin prior mathematics are inherited, not DASHI-invented.
- Existing #772 BIDI recursive selective invalidation/Pareto owner and #1129 polynomial SAT frontier remain independent. Agda #1414 distinct 27→11→7 and parity owners were separately reviewed; no duplicate C2 apparatus is made here.

**New in THIS existing Agda OpenAI-ingestion PR #1212:**
- `DASHI/Research/OpenAIMath/OpenAIMathSharedTseitinUniqueExtensionExact.agda` (commits `537d8b2369f8c37e7fb5d5ddcc08927dd489ca8b`, implicit-index repair `13b64a8bee7ec6bebf9052b608dee711ed7ed8c1`, shared-acceptance extension `3c0a0672971ce365735f0dbbf5bce5411751a363`).
- Exact finite-coordinate carrier distinguishes `Fin inputs` from `Fin gates` and maps to original gate variable numbering. `canonicalAgreementOnUsedCoordinates` directly composes previously constructed `sharedConstraintsGiveRealization` with `assignmentFromProgramInputCorrect`/`GateCorrect`. `uniqueAuxiliaryGateValues` and `uniqueUsedCoordinates` establish pointwise that any two satisfying assignments with equal input vectors agree on every **USED** circuit variable. `acceptedFormulaRealization` and `uniqueAcceptedFormulaModelsOnUsedCoordinates` upgrade the statement to models of the actual shared acceptance formula, not an invented surrogate.
- Focused research `Everything.agda` now imports this source owner via commit `931cd5fd44d9fc10ba6744c0cd2e7ed6971e4519`. No protected ESD/global root edits.
- Independent executable finite test `scripts/check_openai_shared_tseitin_parsimonious.py` committed `c635b177c5b78d4628d7684de62adae730db534e`. An independently authored local equivalent script **EXECUTED and PASSED 59,290 exhaustive small Boolean DAG/output cases**, with gate-only implication and unconstrained-tail negative controls. The GitHub-committed script was not run in the exact checkout; Agda compiler is not installed here; no kernel receipt.

**Genuinely new precise limit:** `Cook.Assignment` is an unbounded `Nat → Bool`, and the shared constraints do not fix its unused tail. Thus literal global uniqueness or equality of counts over ALL `Nat → Bool` assignments would be false/ill-typed as a finite #SAT statement. The source-witness theorem proves uniqueness only on the `inputs + gates` finite support, sufficient as the **functional determination component** of a parsimonious encoding; finite supported-model cardinality and an explicit bijection remain unpaid.

### Updated graded max-cut / Pareto tasks
- [x] Reuse exact older DAG/Tseitin proof terms and prove unique auxiliary extension on all used variable indices (SOURCE-WRITTEN, Agda KERNEL PENDING).
- [x] Preserve original #1040 owner, record independent 59,290-case local computational evidence and negative controls.
- [x] Import the new owner via dedicated OpenAI Research `Everything.agda` while leaving global TOE roots unchanged until kernel acceptance.
- [ ] Kernel-check on pinned Agda/stdlib; eliminate any syntactic/type inference errors, record exact compiler SHA and trusted axiom audit.
- [ ] Finite-support model bijection: formally count *only* valuations of `Fin (inputs+gates)`, and prove acceptance-model cardinality equals accepting-input cardinality with unique auxiliary extension. This is the exact missing #SAT lemma.
- [ ] Connect existing `Cook.BooleanFormula` to bounded-width `OAI.Algorithms.SubexponentialSAT.SAT.CNF (Fin n)` using a computable **parsimonious** CNF compiler. Verify actual literal clause width, variable count (including fresh gates), canonical `Encoding.formulaBitLength` and bit/runtime overhead; ordinary polynomial-time reduction is insufficient to preserve a claimed `2^{o(n)}` bound in the original parameter.
- [ ] Port or witness the OpenAI 378 **source proof** in a separately pinned Lean environment; keep existing Oct-6 `openai/math@1581d4...` vendor immutable until the upgrade is explicitly performed. Upstream actual solution is `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat` in `SqrtLogSpace/Final.lean`, not the Comparator challenge containing `sorry`.
- [ ] Reconcile the graph Max-Cut 102 (variable-size simple unweighted gap theorem) vs our fixed finite orbit objectives; preserve the two-vertex strict-loss counterexample and no automatic approximation-hardness transfer.
- [ ] Source/date audit and selective invalidation via #772; record theorem vs framework, inherited classical art vs original DASHI proof, source-written vs executed vs kernel acceptance.

**Status:** A narrow, high-value conditional bridge is committed. OpenAI's announced ETH refutation is NOT re-proved in Agda; neither #SAT finite counting bijection nor polynomial-encoding/complexity transfer is closed. New source and rollup need exact-head Agda typecheck.
