# Epistemic Consequence Boundary Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Formalise the analytical separation among epistemic uncertainty, consequence severity, and reversibility without inventing a new legal doctrine.

**Architecture:** Add one small SensibLaw analytical owner with explicit coordinate types and non-promotion boundaries. It does not decide whether action is lawful, justified, proportionate, or required; it only prevents severity/reversibility/uncertainty from being silently collapsed.

**Tech Stack:** Agda; existing SensibLaw/Core primitives only.

**Spec:** `docs/superpowers/specs/2026-09-13-institutional-norm-production-fragmentation-design.md`

## Global Constraints

- High consequence does not prove the underlying inference false.
- High uncertainty does not automatically prohibit action.
- Legal availability does not imply adequacy for every downstream consumer.
- Severity and reversibility remain separate coordinates.
- No numeric legal threshold is invented.
- No case-specific outcome is encoded.
- No Agda GREEN without an exact-head execution receipt.

---

### Task 1: RED/GREEN analytical owner

**Files:**
- Create first: `DASHI/Law/SensibLawEpistemicConsequenceBoundaryRegression.agda`
- Create after RED: `DASHI/Law/SensibLawEpistemicConsequenceBoundaryExact.agda`

The regression must require:

```agda
highConsequenceAutomaticallyUnderlyingInferenceFalse = false
highUncertaintyAutomaticallyProhibitsAction = false
legalAvailabilityAutomaticallyAdequateForEveryConsumer = false
severityAndReversibilityAreSeparateCoordinates = true
```

The owner must define separate carriers:

```text
EpistemicUncertainty = low | medium | high | unresolved
ConsequenceSeverity = low | moderate | severe | extreme
Reversibility = readilyReversible | partlyReversible | difficultToReverse | irreversible
```

and a record bundling them without deriving one from another.

---

### Task 2: Validation

Add a narrow roll-up only if reuse requires it; otherwise keep the owner/regression directly targetable. Extend the existing institutional-operation focused workflow or create a tiny dedicated workflow. Keep exact-head certification fail-closed.

## Plan self-review

- No legal doctrine is invented.
- No normative conclusion is inferred from uncertainty/severity alone.
- The owner is analytical and consumer-indexed downstream.
