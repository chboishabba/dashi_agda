# James Sensorimotor Decision/Action Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Formalise James’s 2026 sensorimotor decision/action perspective as a repo-native recurrent sensorimotor/active-sensing bridge over existing DASHI decision, memory, learning, and neural-producer machinery.

**Architecture:** Add one primary Agda owner plus a narrow regression and static contract. The owner reuses `DecisionStateBundleExact`, `MemoryFibre`, `UnifiedDecisionDynamicsExact`, `NeuralDecisionProducerBridgeExact`, and `IntersectionalNonFactorability`; it introduces only the missing environment–sensation–sensorimotor–action recurrence, active-sensing learning witness, and phenomenon/mechanism WrongType boundaries.

**Tech Stack:** Agda, Python 3 focused static checker, GitHub branch `agent/james-sensorimotor-decision-action`.

**Spec:** `docs/superpowers/specs/2026-09-12-james-sensorimotor-decision-action-design.md`

## Global Constraints

- Reuse existing decision/memory/learning owners; do not create a parallel decision ontology.
- Published source DOI is `10.1162/JOCN.a.2484`; preprint DOI `10.20944/preprints202507.0979.v1` is earlier-manifestation metadata only.
- Citation imports neither proof nor authority.
- Keep metaphysical free-will/determinism promotion false.
- Use test-first static contract and do not claim Agda kernel success without a real exact-head receipt.

---

### Task 1: Focused RED contract

**Files:**
- Create: `scripts/check_james_sensorimotor_decision_action.py`

**Interfaces:**
- Consumes: repository text files only.
- Produces: exit 0 only when the James owner, regression, aggregate import, source coordinates, active-sensing recurrence, learning bridge, and WrongType boundaries are present.

- [ ] **Step 1: Write the failing static checker**

Create a Python script that requires these files:

```python
OWNER = "DASHI/Cognition/PNF/JamesSensorimotorDecisionActionExact.agda"
REGRESSION = "DASHI/Cognition/PNF/JamesSensorimotorDecisionActionRegression.agda"
AGGREGATE = "DASHI/Cognition/PNF/PNFIRLearningEverything.agda"
```

Require the owner text to contain all of:

```python
OWNER_NEEDLES = [
    "10.1162/JOCN.a.2484",
    "10.20944/preprints202507.0979.v1",
    "SensorimotorEpisode",
    "activeSensingStep",
    "learningThroughActiveSensing",
    "observedActionDoesNotRecoverSensorimotorState",
    "decisionPhenomenonIsNotMechanism",
    "memoryDescriptionIsNotLearningUpdate",
    "jamesDoesNotProveDeterminism",
    "jamesDoesNotProveLibertarianFreeWill",
]
```

Require the regression to import the owner and contain `canonicalJamesSensorimotorRegression`, and require the aggregate to import `DASHI.Cognition.PNF.JamesSensorimotorDecisionActionExact`.

- [ ] **Step 2: Run the checker and verify RED**

Run:

```bash
python3 scripts/check_james_sensorimotor_decision_action.py
```

Expected result before Task 2: non-zero exit with missing owner/regression and/or missing aggregate import.

- [ ] **Step 3: Commit the RED contract**

```bash
git add scripts/check_james_sensorimotor_decision_action.py
git commit -m "test: add James sensorimotor decision contract"
```

---

### Task 2: James recurrent sensorimotor owner

**Files:**
- Create: `DASHI/Cognition/PNF/JamesSensorimotorDecisionActionExact.agda`

**Interfaces:**
- Consumes:
  - `DASHI.Cognition.PNF.DecisionStateBundleExact`
  - `DASHI.Cognition.PNF.MemoryFibre`
  - `DASHI.Cognition.PNF.UnifiedDecisionDynamicsExact`
  - `DASHI.Biology.NeuralDecisionProducerBridgeExact`
  - `DASHI.Core.IntersectionalNonFactorability`
- Produces:
  - `SensorimotorEpisode`
  - `activeSensingStep`
  - `learningThroughActiveSensing`
  - `observedActionDoesNotRecoverSensorimotorState`
  - source/boundary records and metaphysical non-promotion witnesses.

- [ ] **Step 1: Define a finite recurrent carrier**

Use small finite datatypes for environment/body, sensory state, sensorimotor state, and action, then define:

```agda
record SensorimotorEpisode : Set where
  constructor sensorimotorEpisode
  field
    environment : EnvironmentState
    sensory : SensoryState
    mechanism : SensorimotorState
    action : Decision.ExecutedAction
    learning : Memory.MemoryFibre
```

Do not duplicate fields already supplied by `MemoryFibre` or `DecisionStateBundle`.

- [ ] **Step 2: Add active-sensing recurrence**

Define a finite transition in which emitted action changes the environment/body coordinate and therefore changes subsequent sensory input. Add a theorem whose normal form witnesses that two different actions from the same initial sensory state can produce different next sensory states.

- [ ] **Step 3: Add learning-through-active-sensing witness**

Define:

```agda
learningThroughActiveSensing : Memory.MemoryFibre → Memory.MemoryFibre
learningThroughActiveSensing = Memory.reinforce
```

and prove both that the action weight changes in the chosen finite witness and that `rememberedEvent` is preserved. Reuse existing `MemoryFibre` theorems rather than re-proving a second memory ontology.

- [ ] **Step 4: Add nonfactorability / lossy-action witness**

Construct two `SensorimotorEpisode` values with the same observed action but different mechanism or learning coordinates, then instantiate `NF.NonFactorabilityWitness` so:

```agda
observedActionDoesNotRecoverSensorimotorState :
  NF.FactorsThrough observedActionProjection sensorimotorProjection → ⊥
```

- [ ] **Step 5: Add phenomenon/mechanism and metaphysical firewalls**

Represent source-bounded boolean boundary records with all of these false:

```text
decision phenomenon = mechanism
decision phenomenon = executed action
memory description = physical learning update
attention label = attention mechanism
paper proves determinism
paper proves libertarian free will
one circuit defines decision
```

Add empty-type or distinct-constructor witnesses where the finite model supports stronger separation.

- [ ] **Step 6: Add source manifestation metadata**

Encode the published and preprint DOI strings and mark the published paper as the final manifestation while keeping the preprint distinct. Do not assert a DOI relationship beyond the source metadata.

- [ ] **Step 7: Commit the owner**

```bash
git add DASHI/Cognition/PNF/JamesSensorimotorDecisionActionExact.agda
git commit -m "feat: formalise James sensorimotor decision recurrence"
```

---

### Task 3: Focused regression and aggregate wiring

**Files:**
- Create: `DASHI/Cognition/PNF/JamesSensorimotorDecisionActionRegression.agda`
- Modify: `DASHI/Cognition/PNF/PNFIRLearningEverything.agda`

**Interfaces:**
- Consumes: exports from Task 2.
- Produces: one narrow compile target and one aggregate import path.

- [ ] **Step 1: Write the regression module**

Import the James owner and define `canonicalJamesSensorimotorRegression` as a product/record that references:

```text
active-sensing next-state difference
remembered-event preservation after learning update
same-action/different-sensorimotor-state witness
metaphysical non-promotion boundary
```

The regression should contain no new ontology.

- [ ] **Step 2: Wire the aggregate**

Add exactly:

```agda
import DASHI.Cognition.PNF.JamesSensorimotorDecisionActionExact
```

to `PNFIRLearningEverything.agda`, following the existing import style.

- [ ] **Step 3: Run the static contract**

```bash
python3 scripts/check_james_sensorimotor_decision_action.py
```

Expected: `James sensorimotor decision/action static contract: OK`.

- [ ] **Step 4: Run focused Agda check when available**

Prefer the repository’s existing focused Agda runner against:

```text
DASHI/Cognition/PNF/JamesSensorimotorDecisionActionRegression.agda
```

If no Agda executable or workflow receipt is available, record certification as open rather than claiming GREEN.

- [ ] **Step 5: Commit regression/wiring**

```bash
git add DASHI/Cognition/PNF/JamesSensorimotorDecisionActionRegression.agda DASHI/Cognition/PNF/PNFIRLearningEverything.agda
git commit -m "test: wire James sensorimotor decision regression"
```

---

### Task 4: Final verification and PR

**Files:**
- Review all files created/modified above.

**Interfaces:**
- Consumes: Tasks 1–3.
- Produces: an inspectable branch/PR with explicit mathematical/source/certification status.

- [ ] **Step 1: Re-run the focused static checker**

```bash
python3 scripts/check_james_sensorimotor_decision_action.py
```

Expected: PASS.

- [ ] **Step 2: Verify branch diff is narrow**

Confirm the branch contains only the spec, plan, static checker, owner, regression, and aggregate import needed by this formalisation.

- [ ] **Step 3: Open a draft PR**

PR body must state:

```text
formalises James architecture != proves free will/determinism
citation != proof/authority
observed action != unique internal trajectory
Agda exact-head certification status
```

- [ ] **Step 4: Report exact head and receipts**

Report the branch head SHA, static checker result, and Agda/CI status without promotion beyond the available receipts.
