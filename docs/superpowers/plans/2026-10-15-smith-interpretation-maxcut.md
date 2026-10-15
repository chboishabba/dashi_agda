# Smith Interpretation Max-Cut Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Weld the existing PNF, consumer-adequacy, experimental-design, investigative-Pareto, LegalFollow, Two-Eyed/intersectional and Justice-Lee machinery into a source-bounded Smith statutory-interpretation capstone, with matching SLR runtime receipts.

**Architecture:** One Agda capstone owns only the missing composition and finite countermodels; existing modules remain semantic/source owners. SLR PR #62 gains only runtime receipts for query-indexed informativeness and experiment/acquisition handoff. No scalar authority score or universal interpretation universe is introduced.

**Tech Stack:** Agda; Rust (`sl-core`); existing SensibLaw/SLR persistence/runtime contracts.

**Spec:** `docs/superpowers/specs/2026-10-15-smith-interpretation-maxcut-design.md`

## Global Constraints

- Preserve opinion-level Smith attribution; do not flatten separate reasons into a single HCA proposition.
- Existing source owners retain attribution and authority; cross-pollination does not transfer authorship.
- Simple/full/multilingual complexity does not create authority; informativeness is consumer/query indexed.
- Experimental design and Pareto acquisition create no claim truth, legal authority, access authority or adjudicative authority.
- Australian precedent constrains/treats an interpretation space but does not exhaust logical/semantic candidate generation.
- No new parallel PNF, LegalFollow, evidence, controversy, Pareto or experimental-design backend.

## Review Focus

- A simpler representation may strictly dominate a complex one for one query without becoming universally superior.
- An interpretation lacking direct precedent remains representable as a semantic/logical candidate while legal status stays unresolved or constrained.
- A failed factorisation may trigger experimental discrimination without creating a factual/legal conclusion.
- A Pareto-optimal acquisition route with unknown/unauthorised access must remain non-executable and non-authoritative.
- Smith counterexamples and `literalism`/`contextomy` remain attributed to Edelman J rather than repository-universal legal doctrine.

---

### Task 1: Source-level RED validation surface

**Files:**
- Create: `DASHI/Law/SmithInterpretationConsumerLegalFollowValidation.agda`

**Interfaces:**
- Consumes: existing `AdmissibleConsumerMDLHyperfabricExact`, `IntersectionalNonFactorability`, `RobustExperimentInferenceFrontierExact`, `ITIRInvestigationAcquisitionParetoExact`, `SensibLawLegalFollowProofSearchBridgeExact`, Two-Eyed/intersectional and Justice-Lee boundaries.
- Produces: compile-time dependency on `DASHI.Law.SmithInterpretationConsumerLegalFollowExact` plus named theorem expectations.

- [ ] Write the validation module first, importing the not-yet-existing production owner and asserting the required boundary theorem names.
- [ ] Confirm the dependency is RED by source inspection / unavailable module before production owner is created.
- [ ] Commit the RED contract.

### Task 2: Smith PNF/interpretation/informativeness formal capstone

**Files:**
- Create: `DASHI/Law/SmithInterpretationConsumerLegalFollowExact.agda`

**Interfaces:**
- Consumes: Task 1 contract and existing canonical owners.
- Produces: `OperativeConstellation`, Smith candidate interpretations, query-indexed `AtLeastAsInformative`, parity/strict-dominance witnesses, erased-distinction counterexample, experimental-discriminator handoff, investigative-Pareto handoff, LegalFollow and authority/attribution firewalls.

- [ ] Implement the minimal types and finite witnesses required by Task 1.
- [ ] Reuse existing `FactorsThrough`/counterexample owners rather than define a parallel factorisation relation.
- [ ] Encode Smith source references as attributed strings/receipts only; do not manufacture source text or legal authority.
- [ ] Expose explicit false boundaries for complexity→authority, precedent→candidate-universe, acquisition→residual-payment, structural-distortion→sophistry-intent and machine-synthesis→judgment.
- [ ] Commit production owner.

### Task 3: Aggregate/export and cross-domain regressions

**Files:**
- Modify: `DASHI/Law/SensibLawRealMatterEverything.agda`
- Create: `DASHI/Law/SmithInterpretationConsumerLegalFollowRegression.agda`

**Interfaces:**
- Consumes: Task 2 production owner.
- Produces: focused import/typecheck surface and regression witnesses covering Two-Eyed coordination-without-fusion, query-indexed admissibility, Lee adjudicative boundary, experimental proposal-only status and Pareto non-scalar status.

- [ ] Write regression imports/assertions before export modification.
- [ ] Add the production owner/regression to the focused real-matter aggregate.
- [ ] Commit aggregate/regression.

### Task 4: SLR RED runtime tests

**Files:**
- Modify: `crates/sl-core/tests/consumer_parity_runtime.rs` on PR #62 branch.

**Interfaces:**
- Consumes: existing PR #62 `ConsumerAdequacyReceipt`, parity/asymmetry/counterexample/perturbation receipts.
- Produces: failing tests for `ConsumerInformativenessReceipt`, `RepresentationDominanceReceipt`, and `DiscriminationHandoffReceipt`.

- [ ] Add tests first for query/consumer mismatch rejection, simpler-surface strict dominance, no universal superiority, and experiment/acquisition handoff non-promotion.
- [ ] Confirm tests are RED because runtime types are absent.
- [ ] Commit test contract.

### Task 5: SLR runtime receipt extension

**Files:**
- Modify: `crates/sl-core/src/consumer_parity.rs`

**Interfaces:**
- Consumes: Task 4 tests.
- Produces: runtime query-indexed informativeness/dominance and discrimination handoff receipts.

- [ ] Implement minimal receipt types and validation.
- [ ] Keep `creates_*authority`, `promotes_claim_truth`, and `resolves_residual` false in constructors.
- [ ] Ensure strict dominance requires shared consumer/query family and a reviewed factorisation/discrimination receipt rather than comparing description-length ranks.
- [ ] Commit runtime implementation.

### Task 6: Completion ledger / PR descriptions

**Files:**
- Modify relevant PR bodies only; no new semantic owner.

**Interfaces:**
- Consumes: Tasks 1–5.
- Produces: explicit verification boundary, attribution ledger, reuse map and remaining empirical residuals.

- [ ] Record that source-level RED-first ordering was observed.
- [ ] Report actual compiler/test status only; do not claim kernel/Cargo green if execution is unavailable.
- [ ] State remaining residuals: exact-head Agda/Cargo execution, persisted Smith REAL-MATTER specimen/source materialisation if runtime environment is unavailable, and any unreviewed source-authority payments.
