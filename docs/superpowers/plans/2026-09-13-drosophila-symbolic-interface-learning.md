# Drosophila Symbolic Interface Learning Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Add a source-bounded formal owner for the viral fruit-fly/Python demo that separates connectome execution, symbolic I/O mapping, learning/update, emitted code, parsing/runtime success, task competence, and biological interpretation.

**Architecture:** Reuse the existing MaleCNS effector bridge, Animalexic governance, James active-sensing owner from stacked PR #895, decision-outcome learning, source attribution, and nonfactorability. Add one narrow Biology owner plus one regression and one static checker, then export through `AnimalexicEverything`.

**Tech Stack:** Agda 2.9-style repository modules, Python 3 static contract, GitHub branch/PR workflow.

**Spec:** `docs/superpowers/specs/2026-09-13-drosophila-symbolic-interface-learning-design.md`

## Global Constraints

- Do not introduce a new general planner, decision ontology, or memory ontology.
- Treat the keyboard/token interface as an artificial symbolic actuator, not biological muscle semantics.
- Keep connectome map, executable dynamics, interface decoder, learning rule, source text, Python syntax, runtime result, FizzBuzz correctness, transfer, and general programming competence as distinct types/statuses.
- Keep social/demo attribution separate from scientific connectome authority and from any unverified person-identity match.
- Do not promote source integration to Agda typecheck, executable simulation, or empirical reproduction.
- Preserve #895's determinism/free-will non-promotion boundary.

---

### Task 1: Focused static contract

**Files:**
- Create: `scripts/check_drosophila_symbolic_interface_learning.py`
- Test target: repository source tree on the stacked branch

**Interfaces:**
- Consumes: expected future paths and exact declaration names from the spec.
- Produces: a deterministic checker that fails while the owner/regression/export are absent and passes only when required source surfaces are present.

- [ ] **Step 1: Write the failing static checker**

```python
#!/usr/bin/env python3
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
REQUIRED = {
    "DASHI/Biology/DrosophilaSymbolicInterfaceLearningExact.agda": [
        "record SymbolicInterfaceExperiment",
        "data CompetenceLevel",
        "artificialSymbolicActuator",
        "connectomeDoesNotDetermineExecutableDynamics",
        "emittedCharactersDoNotEstablishPythonKnowledge",
        "fizzBuzzDoesNotEstablishGeneralProgrammingCompetence",
        "connectomeAdvantageRequiresNullComparison",
    ],
    "DASHI/Biology/DrosophilaSymbolicInterfaceLearningRegression.agda": [
        "canonicalDrosophilaSymbolicInterfaceRegression",
    ],
    "DASHI/Biology/AnimalexicEverything.agda": [
        "DrosophilaSymbolicInterfaceLearningExact",
        "DrosophilaSymbolicInterfaceLearningRegression",
    ],
}

errors = []
for rel, needles in REQUIRED.items():
    path = ROOT / rel
    if not path.exists():
        errors.append(f"missing: {rel}")
        continue
    text = path.read_text(encoding="utf-8")
    for needle in needles:
        if needle not in text:
            errors.append(f"{rel}: missing {needle}")

if errors:
    print("\n".join(errors), file=sys.stderr)
    raise SystemExit(1)
print("drosophila symbolic interface static contract: OK")
```

- [ ] **Step 2: Run the checker and verify RED**

Run:

```bash
python3 scripts/check_drosophila_symbolic_interface_learning.py
```

Expected: exit `1` with missing owner/regression declarations.

- [ ] **Step 3: Commit the RED checker**

```bash
git add scripts/check_drosophila_symbolic_interface_learning.py
git commit -m "test: require Drosophila symbolic interface learning"
```

---

### Task 2: Symbolic interface owner

**Files:**
- Create: `DASHI/Biology/DrosophilaSymbolicInterfaceLearningExact.agda`
- Test: `scripts/check_drosophila_symbolic_interface_learning.py`

**Interfaces:**
- Consumes:
  - `DASHI.Biology.DrosophilaMaleCNSEffectorObservationBridge`
  - `DASHI.Biology.AnimalexicDrosophilaEmbodiedBridge`
  - `DASHI.Cognition.PNF.JamesSensorimotorDecisionActionExact`
  - `DASHI.Cognition.PNF.DecisionOutcomeLearningFeedbackExact`
  - `DASHI.Core.AttributedSourceCore`
  - `DASHI.Core.IntersectionalNonFactorability`
- Produces:
  - `CompetenceLevel`
  - `SymbolicInterfaceExperiment`
  - typed assistance/null-model surfaces
  - WrongType/non-promotion witnesses required by the checker.

- [ ] **Step 1: Implement the minimal typed carrier**

Use distinct finite types for `ConnectomeState`, `ExecutableState`, `Symbol`, `ProgramText`, `ParseResult`, `RuntimeResult`, and `CompetenceLevel`. Define `CompetenceLevel` with constructors equivalent to:

```agda
neuralActivityOnly
mappedTokenEmission
nonemptyProgramText
pythonParses
pythonExecutes
fizzBuzzDeclaredCases
fizzBuzzHeldOutCases
crossTaskTransfer
generalProgrammingCompetence
```

Define:

```agda
record SymbolicInterfaceExperiment : Set where
  field
    connectomeReceipt : Fly.ScientificSourceReceipt
    ExecutableState NeuralObservation Symbol ProgramText TaskFeedback : Set
    neuralStep : ExecutableState → ExecutableState
    decodeSymbol : ExecutableState → Symbol
    renderProgram : List Symbol → ProgramText
    evaluateFeedback : ProgramText → TaskFeedback
```

Keep interface semantics explicit through an `ActuatorKind` containing `artificialSymbolicActuator`.

- [ ] **Step 2: Add source/provenance separation**

Create `AttributedSourceCore` objects for the viral/social demo locator and for any implementation locator that is actually source-verified. If only the social claim is currently verified, encode implementation details as unpaid/residual rather than filling them from secondary reporting.

Add an explicit identity boundary so display-name equality cannot promote a social account to a named researcher identity.

- [ ] **Step 3: Add competence and assistance boundaries**

Define a record carrying input encoding, decoder, update rule, reward/evaluator, prompt/scaffold, attempt budget, and selection policy as distinct coordinates.

Add Boolean or empty-type boundaries for:

```text
connectome map != executable dynamics
simulated dynamics != living fly cognition
artificial actuator != biological effector
emitted characters != Python knowledge
valid syntax != task correctness
FizzBuzz success != general programming competence
successful run != learned policy
learning update != biological synaptic plasticity
social caption != technical receipt
secondary report != primary implementation proof
connectome-derived success != causal connectome advantage
```

- [ ] **Step 4: Add null-model obligation surface**

Define a finite `NullModelKind` including degree-preserving rewiring, shuffled identity, matched generic recurrent network, no-learning decoder control, and alternate initialization. Define `connectomeAdvantageRequiresNullComparison` as a fail-closed boundary rather than an empirical success claim.

- [ ] **Step 5: Re-run static checker**

Run:

```bash
python3 scripts/check_drosophila_symbolic_interface_learning.py
```

Expected: still FAIL because regression/export are not yet present, but the owner-specific missing declarations disappear.

- [ ] **Step 6: Commit owner**

```bash
git add DASHI/Biology/DrosophilaSymbolicInterfaceLearningExact.agda
git commit -m "feat: formalise Drosophila symbolic interface learning"
```

---

### Task 3: Regression and aggregate export

**Files:**
- Create: `DASHI/Biology/DrosophilaSymbolicInterfaceLearningRegression.agda`
- Modify: `DASHI/Biology/AnimalexicEverything.agda`
- Test: `scripts/check_drosophila_symbolic_interface_learning.py`

**Interfaces:**
- Consumes: Task 2 owner.
- Produces: `canonicalDrosophilaSymbolicInterfaceRegression` and aggregate visibility.

- [ ] **Step 1: Write focused regression**

The regression record must witness at least:

```agda
record DrosophilaSymbolicInterfaceRegression : Set where
  field
    symbolicActuatorRemainsArtificial : ...
    fizzBuzzDoesNotPromoteGeneralCompetence : ...
    socialClaimDoesNotCreateScientificAuthority : ...
    connectomeAdvantageStillNeedsNulls : ...
    jamesMetaphysicalBoundaryPreserved : ...
```

Construct `canonicalDrosophilaSymbolicInterfaceRegression` from the owner and #895 witnesses.

- [ ] **Step 2: Export through AnimalexicEverything**

Add:

```agda
open import DASHI.Biology.DrosophilaSymbolicInterfaceLearningExact
open import DASHI.Biology.DrosophilaSymbolicInterfaceLearningRegression
```

following the file's existing import style.

- [ ] **Step 3: Run static checker and verify GREEN**

Run:

```bash
python3 scripts/check_drosophila_symbolic_interface_learning.py
```

Expected: exit `0`, printing `drosophila symbolic interface static contract: OK`.

- [ ] **Step 4: Run focused Agda checks**

Run, if the repository toolchain is available:

```bash
agda -i . DASHI/Biology/DrosophilaSymbolicInterfaceLearningExact.agda
agda -i . DASHI/Biology/DrosophilaSymbolicInterfaceLearningRegression.agda
```

Expected: both exit `0`. If Agda is unavailable, record that as an unpaid certification status and do not claim typechecking.

- [ ] **Step 5: Commit regression/export**

```bash
git add DASHI/Biology/DrosophilaSymbolicInterfaceLearningRegression.agda DASHI/Biology/AnimalexicEverything.agda
git commit -m "test: regress Drosophila symbolic interface boundaries"
```

---

### Task 4: Source audit and PR handoff

**Files:**
- Modify only if source audit finds a factual correction: `DASHI/Biology/DrosophilaSymbolicInterfaceLearningExact.agda`
- No new ontology files.

**Interfaces:**
- Consumes: implementation and exact online source evidence.
- Produces: final fail-closed source/payment status in the draft PR description.

- [ ] **Step 1: Audit all encoded claims against source roles**

Check that the connectome papers pay structural facts, the social/demo source pays only what is visible in the demo/post, implementation details are paid only by implementation-first-party material, and secondary media are locator/context sources only.

- [ ] **Step 2: Verify no person-identity collapse**

Search the owner for any statement equating a social handle/display name with a researcher. There must be none without a primary same-object identity receipt.

- [ ] **Step 3: Re-run verification commands**

Run the static checker and focused Agda commands from Task 3. Record exact outputs/statuses.

- [ ] **Step 4: Open/update stacked draft PR**

Base the PR on `agent/james-sensorimotor-decision-action` so the diff contains only this Fly specialization. State separately: source integration, static-contract status, Agda status, executable-simulation status, and empirical-reproduction status.
