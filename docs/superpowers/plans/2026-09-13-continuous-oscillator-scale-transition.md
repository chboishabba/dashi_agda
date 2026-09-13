# Continuous Oscillator Refinement and Recursive Scale Transition Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Implement the approved typed recursive scale-transition interface and continuous oscillator memory-refinement layer without collapsing existing DASHI semantic, energy, phase, or empirical boundaries.

**Architecture:** Add one generic core owner for `state -> trajectory -> persistent class -> realized next-scale object`, then add one cognition owner that treats continuous oscillator structure as a hidden refinement beneath the existing public memory/phase carriers. Keep learning objective, update law, observation, stability, and semantic realization as separate typed surfaces; verify those separations in one focused regression before any rollup wiring.

**Tech Stack:** Agda, existing DASHI cognition/core modules, repository regression pattern, GitHub branch `agent/continuous-oscillator-scale-transition`.

**Spec:** `docs/superpowers/specs/2026-09-13-continuous-oscillator-scale-transition-design.md`

## Global Constraints

- `MemoryFibre` remains the public cognitive memory carrier.
- `PhaseEnrichedTrit` remains finite and is not promoted to a Hilbert space or physical quantum implementation.
- `UnifiedEnergyFunctionalSurface` remains a coordination interface and is not merged with the new cognitive objective carrier.
- Stable learned structures may be attractors, invariant sets, metastable classes, phase-locked sets, quotient classes, or other persistent classes; fixed points are not universalized.
- Target/reference states are present-time encoded constraints; no backwards-in-time causal claim is introduced.
- Gradient descent is not definitionally Hebbian/Oja/Kuramoto learning.
- Phase coherence is not definitionally truth, empirical adequacy, or cognitive dissonance.
- Continuous phase is not definitionally the existing `Phase3`.
- No real/complex oscillator numerics, EEG/MEG fitting, CRT Hilbert/module projectors, Levin-specific realization, or empirical promotion is introduced in this tranche.

---

## File Structure

- Create `DASHI/Core/RecursiveScaleTransitionExact.agda`
  - Owns the generic indexed scale-transition carrier and witness-mediated realization boundary.
- Create `DASHI/Cognition/PNF/ContinuousOscillatorMemoryRefinementExact.agda`
  - Owns the hidden oscillator schema, stable-class semantics, objective/update/measurement separation, and projection to existing cognition carriers.
- Create `DASHI/Cognition/PNF/ContinuousOscillatorMemoryRefinementRegression.agda`
  - Owns focused compile-time witnesses and WrongType/non-collapse checks.
- Modify only the narrow cognition/core rollup that already imports nearby owners, after focused regression passes.

---

### Task 1: RED regression for recursive scale transition

**Files:**
- Create: `DASHI/Cognition/PNF/ContinuousOscillatorMemoryRefinementRegression.agda`
- Target owner to be created later: `DASHI/Core/RecursiveScaleTransitionExact.agda`

**Interfaces:**
- Consumes: existing Agda prelude/equality only.
- Produces required names: `RecursiveScaleTransition`, `SituatedLowerState`, `PersistentRole`, `realiseNextObject`, `persistenceNeedNotBeAttractor`.

- [ ] **Step 1: Write the failing regression import and witness surface**

```agda
module DASHI.Cognition.PNF.ContinuousOscillatorMemoryRefinementRegression where

open import Agda.Builtin.Equality using (_≡_; refl)
import DASHI.Core.RecursiveScaleTransitionExact as Scale

scaleTransitionSurfaceExists : Set₁
scaleTransitionSurfaceExists = Scale.RecursiveScaleTransition
```

- [ ] **Step 2: Run the focused regression and verify RED**

Run:
```bash
agda -i . -i DCHoTT-Agda -i cubical -l standard-library DASHI/Cognition/PNF/ContinuousOscillatorMemoryRefinementRegression.agda
```

Expected: FAIL because `DASHI.Core.RecursiveScaleTransitionExact` does not yet exist.

- [ ] **Step 3: Commit the RED regression**

```bash
git add DASHI/Cognition/PNF/ContinuousOscillatorMemoryRefinementRegression.agda
git commit -m "test: require recursive scale transition surface"
```

---

### Task 2: Implement generic recursive scale transition owner

**Files:**
- Create: `DASHI/Core/RecursiveScaleTransitionExact.agda`
- Modify: `DASHI/Cognition/PNF/ContinuousOscillatorMemoryRefinementRegression.agda`

**Interfaces:**
- Consumes: only Agda builtins needed for records/equality/string labels.
- Produces:
  - `SituatedLowerState`
  - `PersistentRole`
  - `RecursiveScaleTransition`
  - `ScaleTransitionWitness`
  - `realiseNextObject`
  - explicit boundary record showing persistence is not next-scale identity by definition and need not be an attractor.

- [ ] **Step 1: Implement the situated state and persistence-role carriers**

```agda
record SituatedLowerState
  (State Environment History : Set) : Set where
  constructor situatedLowerState
  field
    state : State
    environment : Environment
    history : History

data PersistentRole : Set where
  orbitClass invariantSet metastableClass resonanceClass
  symmetrySector quotientClass attractorClass : PersistentRole
```

- [ ] **Step 2: Implement the transition record with explicit D/A/Q stages**

```agda
record RecursiveScaleTransition
  (State Environment History Trajectory Persistent Next : Set) : Set₁ where
  field
    dynamics : SituatedLowerState State Environment History → Trajectory
    classifyPersistent : Trajectory → Persistent
    persistentRole : Persistent → PersistentRole
    RealisesNext : Persistent → Next → Set
    realiseNextObject : (p : Persistent) → Σ Next (RealisesNext p)
```

Use `Agda.Builtin.Sigma` for `Σ` rather than inventing a local pair.

- [ ] **Step 3: Add explicit non-collapse boundaries**

```agda
record RecursiveScaleTransitionBoundary : Set₁ where
  field
    persistenceIsNotNextIdentityByDefinition : Set
    persistenceNeedNotBeFixedPoint : Set
    persistenceNeedNotBeAttractor : Set
    environmentRemainsExplicit : Set
    historyRemainsExplicit : Set
    noUniversalPhysicalF : Set
```

- [ ] **Step 4: Extend regression with a finite witness**

Construct tiny `data` carriers for lower state, environment, history, trajectory, persistence, and next object; instantiate `RecursiveScaleTransition`; prove the next object is obtained only through `RealisesNext`/`realiseNextObject`.

- [ ] **Step 5: Run focused regression**

Run the same Agda command as Task 1.

Expected: PASS for the scale-transition portion.

- [ ] **Step 6: Commit**

```bash
git add DASHI/Core/RecursiveScaleTransitionExact.agda DASHI/Cognition/PNF/ContinuousOscillatorMemoryRefinementRegression.agda
git commit -m "feat: add typed recursive scale transition"
```

---

### Task 3: RED regression for continuous oscillator refinement

**Files:**
- Modify: `DASHI/Cognition/PNF/ContinuousOscillatorMemoryRefinementRegression.agda`
- Target owner to be created later: `DASHI/Cognition/PNF/ContinuousOscillatorMemoryRefinementExact.agda`

**Interfaces:**
- Consumes from Task 2: `RecursiveScaleTransition`.
- Produces required oscillator names: `OscillatorSchema`, `HiddenOscillatorState`, `StableLearnedClass`, `OscillatorObjectiveSurface`, `OscillatorMemoryRefinement`, `ContinuousOscillatorBoundary`.

- [ ] **Step 1: Add the missing owner import**

```agda
import DASHI.Cognition.PNF.ContinuousOscillatorMemoryRefinementExact as Osc
```

- [ ] **Step 2: Require named type surfaces in the regression**

```agda
oscillatorSchemaSurfaceExists : Set₁
oscillatorSchemaSurfaceExists = Osc.OscillatorSchema

continuousBoundarySurfaceExists : Set₁
continuousBoundarySurfaceExists = Osc.ContinuousOscillatorBoundary
```

- [ ] **Step 3: Run focused regression and verify RED**

Expected: FAIL because the oscillator owner does not exist.

- [ ] **Step 4: Commit the RED extension**

```bash
git add DASHI/Cognition/PNF/ContinuousOscillatorMemoryRefinementRegression.agda
git commit -m "test: require continuous oscillator refinement surface"
```

---

### Task 4: Implement continuous oscillator schema and hidden state

**Files:**
- Create: `DASHI/Cognition/PNF/ContinuousOscillatorMemoryRefinementExact.agda`

**Interfaces:**
- Consumes existing cognition owners after exact path verification: `MemoryFibre`, `PhaseEnrichedTrit`, and narrow learning surfaces already used by nearby PNF modules.
- Produces:
  - `OscillatorSchema`
  - `HiddenOscillatorState`
  - abstract amplitude/frequency/phase/coupling coordinates
  - superposition constructor type
  - hidden-state equivalence relation.

- [ ] **Step 1: Define a structural oscillator schema without pretending Agda builtins are reals/complexes**

```agda
record OscillatorSchema : Set₁ where
  field
    Mode Amplitude Frequency ContinuousPhase Coupling HiddenField : Set
    assembleMode : Mode → Amplitude → Frequency → ContinuousPhase → Coupling → HiddenField
```

- [ ] **Step 2: Define a hidden state with explicit environment/history-compatible coordinates**

```agda
record HiddenOscillatorState (O : OscillatorSchema) : Set where
  field
    hiddenField : OscillatorSchema.HiddenField O
```

Add only structural fields needed by the approved spec; do not introduce fake numeric operations.

- [ ] **Step 3: Add generic hidden-state equivalence and observer soundness types**

```agda
record HiddenObservationQuotient
  (Hidden Public : Set) : Set₁ where
  field
    EquivalentHiddenState : Hidden → Hidden → Set
    observe : Hidden → Public
    observerSound : ∀ x y → EquivalentHiddenState x y → observe x ≡ observe y
```

- [ ] **Step 4: Document intended numerical realization in comments**

Include exactly the non-promoted notation:

```text
psi_i(t) = A_i exp(i(omega_i t + phi_i))
Psi(t)   = sum_i w_i psi_i(t)
```

and state that no complex-analysis implementation is claimed here.

- [ ] **Step 5: Run focused regression**

Expected: remaining failures should now concern stable-class/objective/refinement names, not base oscillator schema.

- [ ] **Step 6: Commit**

```bash
git add DASHI/Cognition/PNF/ContinuousOscillatorMemoryRefinementExact.agda
git commit -m "feat: add structural oscillator hidden carrier"
```

---

### Task 5: Add stable-class and learning/objective/measurement separation

**Files:**
- Modify: `DASHI/Cognition/PNF/ContinuousOscillatorMemoryRefinementExact.agda`
- Modify: `DASHI/Cognition/PNF/ContinuousOscillatorMemoryRefinementRegression.agda`

**Interfaces:**
- Consumes Task 4 oscillator schema.
- Produces:
  - `StableLearnedClass`
  - `StabilityRole`
  - `OscillatorObjectiveSurface`
  - `LearningUpdateWitness`
  - `ObservedCognitiveMeasurement`
  - explicit non-identity boundaries.

- [ ] **Step 1: Define stability roles broader than minima**

```agda
data StabilityRole : Set where
  localMinimum flatMinimum metastable phaseLocked limitCycleModGauge
  invariantLearnedClass : StabilityRole

record StableLearnedClass (Hidden : Set) : Set₁ where
  field
    LearnedClass : Set
    classify : Hidden → LearnedClass
    role : LearnedClass → StabilityRole
```

- [ ] **Step 2: Separate objective, update, and observed measurement**

```agda
record OscillatorObjectiveSurface (Hidden : Set) : Set₁ where
  field
    Objective : Set
    objective : Hidden → Objective

record LearningUpdateWitness (Hidden : Set) : Set₁ where
  field
    update : Hidden → Hidden

record ObservedCognitiveMeasurement : Set₁ where
  field
    Measurement : Set
```

- [ ] **Step 3: Add the approved WrongType/non-promotion boundary record**

```agda
record ContinuousOscillatorBoundary : Set₁ where
  field
    continuousPhaseIsNotPhase3ByDefinition : Set
    mismatchIsNotCognitiveDissonanceByDefinition : Set
    gradientDescentIsNotHebbianByDefinition : Set
    coherenceIsNotTruthByDefinition : Set
    stableClassIsNotMinimumByDefinition : Set
    targetStateIsNotBackwardsCausation : Set
    objectiveDoesNotMergeAllEnergyCarriers : Set
```

- [ ] **Step 4: Extend regression to require every boundary field by projection**

For each boundary field, create a regression function that accepts `ContinuousOscillatorBoundary` and returns that field. This checks names/types without postulating witnesses.

- [ ] **Step 5: Run focused regression**

Expected: PASS for stability/objective/boundary names; remaining work should be public-memory refinement.

- [ ] **Step 6: Commit**

```bash
git add DASHI/Cognition/PNF/ContinuousOscillatorMemoryRefinementExact.agda DASHI/Cognition/PNF/ContinuousOscillatorMemoryRefinementRegression.agda
git commit -m "feat: separate oscillator learning objective and observation"
```

---

### Task 6: Bridge hidden oscillator state to existing memory/phase carriers

**Files:**
- Modify: `DASHI/Cognition/PNF/ContinuousOscillatorMemoryRefinementExact.agda`
- Modify: `DASHI/Cognition/PNF/ContinuousOscillatorMemoryRefinementRegression.agda`

**Interfaces:**
- Consumes: exact existing `MemoryFibre` and `PhaseEnrichedTrit` definitions after fetching their current owner paths on the branch.
- Produces: `OscillatorMemoryRefinement` and witness that hidden coordinate changes may preserve public memory identity.

- [ ] **Step 1: Fetch the exact current memory owner and copy its real type signature into this task before editing**

Run repository search for `record MemoryFibre` and fetch the owner. Do not guess constructor fields or module path.

- [ ] **Step 2: Define the refinement record parametrically over the actual public memory type**

The record must have this logical shape:

```agda
record OscillatorMemoryRefinement
  (Hidden Public : Set) : Set₁ where
  field
    observeMemory : Hidden → Public
    EquivalentHiddenState : Hidden → Hidden → Set
    preservedObservation :
      ∀ x y → EquivalentHiddenState x y → observeMemory x ≡ observeMemory y
```

If the existing `MemoryFibre` is parameterized, instantiate `Public` with its exact current type instead of introducing a parallel memory ontology.

- [ ] **Step 3: Add a separate optional finite-phase observation seam**

Map hidden continuous states to an existing `PhaseEnrichedTrit` or its public observation only through an explicit function supplied by the refinement; do not identify `ContinuousPhase` with `Phase3`.

- [ ] **Step 4: Add a finite regression witness**

Construct two distinct hidden test states declared equivalent by a tiny test relation and prove they project to the same public test-memory value. Also require that scale-transition realization remains witness-mediated.

- [ ] **Step 5: Run focused regression**

Expected: PASS.

- [ ] **Step 6: Commit**

```bash
git add DASHI/Cognition/PNF/ContinuousOscillatorMemoryRefinementExact.agda DASHI/Cognition/PNF/ContinuousOscillatorMemoryRefinementRegression.agda
git commit -m "feat: refine oscillator state into public memory carrier"
```

---

### Task 7: Narrow rollup integration

**Files:**
- Modify: the nearest existing cognition PNF rollup that already imports sibling PNF exact owners, determined by repository search.
- Optionally modify: the nearest core rollup for reusable scale-transition machinery only if the repo has an established exact-owner rollup pattern.

**Interfaces:**
- Consumes: both new exact owners.
- Produces: discoverability only; no new semantics.

- [ ] **Step 1: Locate the narrow rollup**

Search for imports of sibling modules under `DASHI/Cognition/PNF/` and choose the smallest established rollup. Do not edit `DASHI/Everything.agda` directly unless that is the existing repository convention for the selected owner family.

- [ ] **Step 2: Add only import lines**

Add:

```agda
import DASHI.Cognition.PNF.ContinuousOscillatorMemoryRefinementExact
```

and, where appropriate:

```agda
import DASHI.Core.RecursiveScaleTransitionExact
```

No aliases, wrappers, duplicate records, or promotion claims.

- [ ] **Step 3: Re-run focused regression**

Expected: PASS.

- [ ] **Step 4: Run the narrow rollup compile**

Run Agda against the modified rollup with the repository's normal include/library flags.

Expected: PASS, or record exact pre-existing/environmental failure without treating it as feature success.

- [ ] **Step 5: Commit**

```bash
git add <chosen-rollup-files>
git commit -m "chore: wire oscillator refinement owners into rollups"
```

---

### Task 8: Verification and completion receipt

**Files:**
- No semantic code changes expected.
- Update plan checkboxes only if repository convention permits; otherwise leave the plan immutable and report verification in PR conversation.

**Interfaces:**
- Consumes: completed branch.
- Produces: evidence-backed completion status.

- [ ] **Step 1: Run focused Agda regression from branch head**

```bash
agda -i . -i DCHoTT-Agda -i cubical -l standard-library DASHI/Cognition/PNF/ContinuousOscillatorMemoryRefinementRegression.agda
```

Expected: exit 0.

- [ ] **Step 2: Run diff hygiene**

```bash
git diff --check master...HEAD
```

Expected: no output, exit 0.

- [ ] **Step 3: Attempt bounded aggregate compile**

Compile the narrow modified rollup first. If appropriate and budget permits, attempt:

```bash
timeout 30s agda -i . -i DCHoTT-Agda -i cubical -l standard-library DASHI/Everything.agda
```

Expected handling: exit 0 = aggregate green; timeout = inconclusive; compile error = investigate and fix if caused by this tranche.

- [ ] **Step 4: Verify branch diff contains only approved scope**

Expected changed semantic files: the two exact owners, one regression, and minimal rollup imports; docs/spec/plan remain design artifacts.

- [ ] **Step 5: Report exact proof status on PR #896**

State separately:
- focused Agda result;
- narrow rollup result;
- aggregate result;
- `git diff --check` result;
- explicit deferred/non-promoted claims.

Do not claim empirical neuroscience, FEP equivalence, complex-wave numerics, quantum implementation, or Hebbian identity.
