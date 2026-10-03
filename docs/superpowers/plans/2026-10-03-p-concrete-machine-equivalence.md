# P Concrete-Machine Equivalence Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Make executable first-match semantics extensionally coincide with relational `MachineStep` on deterministic normalized concrete machines, then isolate standard-TM polynomial simulation as the sole remaining model-equivalence theorem.

**Architecture:** Add a focused rule-key determinism owner over the existing `ConcreteTapeMachine.rules`, prove first-match completeness/uniqueness, and consume it in the intrinsic operational-step owner. Do not change the machine carrier or Cook–Levin semantics.

**Tech Stack:** Agda, existing DASHI complexity modules.

**Spec:** `docs/superpowers/specs/2026-10-03-p-concrete-machine-equivalence-design.md`

## Global Constraints
- Reuse `ConcreteTapeMachine` and `MachineStep` unchanged.
- No postulates, holes, unsafe termination, or synthetic lower-bound assumptions.
- Keep all theorem statements same-object with the literal machine rule list.

## Review Focus
- Duplicate identical keys with distinct target/write/direction must be rejected by determinism.
- Duplicate literally identical rules must not break first-match equivalence.
- Missing key must produce `nothing` and no relational step on that key.
- Equality-decider soundness must be sufficient; do not assume completeness beyond existing refl/sound fields unless proved.
- Intrinsic row proof must preserve existing well-formedness/margin invariants.

---

### Task 1: Rule-key determinism and first-match completeness

**Files:**
- Create: `DASHI/Mathematics/Complexity/PNotEqualsNPConcreteTapeRuleKeyDeterminismExact.agda`
- Modify: `DASHI/Mathematics/CrossPollination/MillenniumSubstantiveCrossPollinationValidation.agda`

**Interfaces:**
- Consumes: `Local.RuleOccurs`, `Interpreter.scanRuleTable`, finite state/symbol equality deciders.
- Produces: `RuleKeyDeterministic machine`; theorem that any occurring rule matching `(q,a)` equals the rule returned by successful first-match lookup; theorem that no successful lookup implies no matching occurring rule.

- [ ] Write theorem signatures and executable regression examples for unique-key, duplicate-identical, duplicate-conflicting, and missing-key tables.
- [ ] Verify the new owner fails to typecheck until the determinism proofs are supplied.
- [ ] Implement recursive uniqueness/completeness lemmas over the literal rule list.
- [ ] Kernel-check the focused file.
- [ ] Commit.

### Task 2: Executable iff relational step

**Files:**
- Modify: `DASHI/Mathematics/Complexity/PNotEqualsNPConcreteTapeIntrinsicOperationalStepExact.agda`

**Interfaces:**
- Consumes: Task 1 uniqueness theorem; intrinsic row parser; `executeUniqueMarginRowWithDecay`.
- Produces: deterministic-machine theorem `execute ... = just result ↔ WellFormedMachineStep machine row result.after` with the matching-key/interior hypotheses made explicit and minimal.

- [ ] Add the converse theorem statement and a regression that chooses a non-first duplicate to ensure determinism is genuinely required.
- [ ] Verify failure without the Task 1 hypothesis.
- [ ] Implement the converse by recovering the relational rule key from `RuleRealizesWindow`, applying first-match uniqueness, and transporting the output row equality.
- [ ] Kernel-check the owner and cumulative validation root.
- [ ] Commit.

### Task 3: Freeze the remaining model-equivalence boundary

**Files:**
- Create or update a focused boundary owner only if an existing standard-TM carrier is found during implementation.

**Interfaces:**
- Produces: exact statement of the two polynomial simulations and clock inequalities; no proof unless an existing carrier/API supports it.

- [ ] Search repository for a standard deterministic TM carrier before introducing any new one.
- [ ] If present, state same-language simulations and clock transport against `ConcreteTapeMachine`; otherwise document the missing carrier without adding a fake implementation.
- [ ] Kernel-check any source-written boundary theorem.
- [ ] Commit.
