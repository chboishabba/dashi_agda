# Federated Subsidiarity Governance Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Add a reusable Agda governance owner for local issue scope, subsidiarity, federation composition, coordination-load decomposition, transition reachability and abstract viability envelopes.

**Architecture:** Reuse `AuthorityMandateCore` and `SituatedConstituency`; add one focused exact owner plus one finite regression owner. Keep all empirical superiority, legitimacy and ecological claims outside the proof kernel unless supplied as explicit witnesses.

**Tech Stack:** Agda 2.9-style source, DASHI core prelude, existing governance receipt/authority modules.

**Spec:** `docs/superpowers/specs/2026-10-05-federated-subsidiarity-governance-design.md`

## Global Constraints

- Do not duplicate authority/mandate or situated-constituency semantics.
- Do not assert a quantitative social-science scaling law from the transcript.
- Do not treat consensus, democracy, federation, legitimacy or ecological viability as definitionally equivalent.
- Keep source-derived motivation separate from DASHI-derived structural theorems.
- New source-written code is not kernel-certified until an exact-head Agda check exists.

## Review Focus

- Local issue with a non-member participant must be rejected by the subsidiarity theorem.
- Boundary/global issues must not accidentally inherit the local-only exclusion theorem.
- Coordination load must not hide a stronger empirical complexity claim than its definition supports.
- Transition reachability must be reflexive and closed under one supplied transition.
- Viability must remain an abstract conjunction of independently supplied predicates.

---

### Task 1: Regression surface

**Files:**
- Create: `DASHI/Governance/FederatedSubsidiarityGovernanceRegression.agda`

**Interfaces:**
- Consumes: intended names from Task 2.
- Produces: finite compile-time examples for local exclusion, reachability and load decomposition.

- [ ] Write the regression module against the intended API before the production owner exists.
- [ ] Verify RED by observing the module cannot resolve `DASHI.Governance.FederatedSubsidiarityGovernanceExact` on the regression-only commit when an Agda runner is available.
- [ ] Commit the regression-only state.

### Task 2: Exact governance owner

**Files:**
- Create: `DASHI/Governance/FederatedSubsidiarityGovernanceExact.agda`

**Interfaces:**
- Produces: `IssueScope`, `FederatedGovernance`, `SubsidiarityWitness`, `nonMemberCannotParticipateLocal`, `federatedLoad`, `federatedLoadUpperBound`, `ComposablePair`, `pairGuarantees`, `TransitionKind`, `TransitionSystem`, `Reachable`, `ViabilityEnvelope`.

- [ ] Implement the minimal data/record layer required by the regression.
- [ ] Prove only definitional/witness-driven theorems.
- [ ] Add a non-promoting `GenericReceipt` and explicit authority/source boundary booleans.
- [ ] Run focused Agda check when available: `agda -i . DASHI/Governance/FederatedSubsidiarityGovernanceRegression.agda`.
- [ ] Commit.

### Task 3: Governance aggregate

**Files:**
- Modify: `DASHI/Governance/Everything.agda`

**Interfaces:**
- Consumes: Task 2 exact owner and Task 1 regression.
- Produces: repository-wide governance aggregation exposure.

- [ ] Import exact owner and regression.
- [ ] Run focused aggregate check when available: `agda -i . DASHI/Governance/Everything.agda`.
- [ ] Commit.

### Task 4: Verification and PR boundary

- [ ] Inspect branch diff for accidental empirical promotion or duplicated authority semantics.
- [ ] Check exact-head workflow status if GitHub Actions surfaces a run.
- [ ] Open a PR describing source-derived motivation, proved structural results and remaining empirical/source residuals.
