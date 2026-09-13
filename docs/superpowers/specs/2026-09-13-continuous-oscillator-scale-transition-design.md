# Continuous Oscillator Refinement and Recursive Scale Transition

Date: 2026-09-13
Branch: `agent/continuous-oscillator-scale-transition`

## Purpose

Add a typed continuous oscillator/refinement layer beneath DASHI's existing cognition memory/phase machinery, and add a generic recursive scale-transition interface that expresses the already-established pattern:

`dynamics -> persistent/invariant class -> observer/quotient -> next-scale effective object`

without identifying all domains with one universal physical mechanism.

This design intentionally preserves existing firewalls:

- `MemoryFibre` remains the public cognitive memory carrier.
- `PhaseEnrichedTrit` remains a finite hidden-phase carrier and is not promoted to a Hilbert space or quantum implementation.
- `UnifiedEnergyFunctionalSurface` remains a coordination surface, not a merger of all energy carriers.
- Attractor language is not universalized: invariant sets, metastable classes, orbits, quotient classes, and attractors remain distinct where required.
- Predictive/goal-directed constraints remain present-time encoded targets; no backwards-in-time causal claim is introduced.

## Architecture

### 1. Generic scale transition

Introduce a reusable owner that refines the informal equation

`S_(n+1) = F(S_n)`

into a level-indexed typed interface:

`F_n = Q_n o A_n o D_n`

where:

- `D_n` maps a lower-scale state/environment/history bundle to a trajectory or evolution witness;
- `A_n` classifies a persistent/stable/invariant structure in that trajectory;
- `Q_n` maps the invariant class through an explicit observer/realisation witness to a next-scale effective object.

The interface must not require that every stable object is an attractor. It should parameterize the persistence notion so domains can supply orbit, invariant-set, metastable, resonance, symmetry-sector, quotient, or attractor witnesses.

The interface must retain environment/history explicitly rather than collapsing them into the state by definition.

### 2. Continuous oscillator refinement carrier

Add a cognition owner representing a continuous hidden oscillator state. The initial formal Agda carrier is deliberately structural rather than numerical: it records domains/types and laws needed for a numerical producer later, without pretending Agda's `Nat` phase is already a real/complex field.

The carrier exposes:

- oscillator mode identity;
- amplitude coordinate;
- frequency coordinate;
- phase coordinate;
- coupling/weight coordinate;
- a superposition/state constructor;
- an observation/refinement map into existing `MemoryFibre` and/or `PhaseEnrichedTrit` surfaces;
- a proof boundary stating that continuous phase is not definitionally the existing `Phase3`.

The module should make the intended mathematical realization explicit in comments/documentation:

`psi_i(t) = A_i exp(i(omega_i t + phi_i))`

`Psi(t) = sum_i w_i psi_i(t)`

but should not postulate complex analysis in Agda merely to imitate notation. A runtime/numerical producer can later discharge those quantities.

### 3. Learning / energy seam

Do not define cognitive dissonance as the energy functional by identity. Instead introduce typed separation between:

- hidden oscillator mismatch / objective value;
- learning/update witness;
- observed cognitive/behavioural measurement.

The continuous model should expose a generic objective carrier compatible with the repo's existing Lyapunov skeleton. The intended numerical objective is conceptually decomposed as:

`F = prediction_error + phase_coupling + amplitude_regularization + smoothness_regularization`

rather than the earlier `||Psi_new - Psi_existing||^2` alone, because the latter admits a trivial inertia optimum.

Any later claim that a concrete update is Hebbian/Oja/Kuramoto-like must be a derived bridge theorem/receipt, not a definitional equality.

### 4. Stable learned state

Do not define memory as a local minimum. The generic learned object is a stable equivalence class of dynamics, allowing:

- local minima;
- flat minima/manifolds;
- metastable states;
- phase-locked sets;
- limit cycles modulo gauge;
- other invariant classes.

The existing `MemoryFibre` remains the semantic/public memory object. The oscillator carrier refines it through an explicit projection/realisation witness.

### 5. Gauge and observation boundary

The design records that a future numerical implementation must handle possible symmetries such as:

- global phase shift;
- time-origin shift;
- amplitude/weight rescaling when both are free.

Agda should not claim these are symmetries unless a concrete realization proves them. Instead, the owner should type a generic `EquivalentHiddenState` relation and require an observer soundness witness showing equivalent hidden states map to the same public observation when appropriate.

### 6. No universal cosmic `F`

The generic recursion is a family `F_n`, not one universal mechanism. The owner should encode that the next-scale object requires a realization/observer witness rather than simply identifying an attractor with the next object.

This matches the existing cell-state architecture, where an attractor requires a separate `AttractorRealisesCellType` witness, and the quantum no-global-attractor boundary, where invertible nontrivial dynamics cannot collapse globally to one fixed point.

## Proposed files

Primary new owners:

- `DASHI/Core/RecursiveScaleTransitionExact.agda`
  - generic state -> trajectory -> invariant class -> next-scale object interface;
  - environment/history explicit;
  - attractor/non-attractor persistence left abstract;
  - non-promotion boundaries.

- `DASHI/Cognition/PNF/ContinuousOscillatorMemoryRefinementExact.agda`
  - hidden continuous-oscillator schema;
  - refinement to existing memory/phase surfaces;
  - objective/update/measurement separation;
  - stable-class rather than minimum-only learning semantics;
  - explicit WrongType-style boundaries.

Focused regression/integration:

- `DASHI/Cognition/PNF/ContinuousOscillatorMemoryRefinementRegression.agda`
  - compile-time witnesses that public memory identity can be preserved while hidden phase/coupling state changes;
  - verifies no definitional collapse of continuous phase into `Phase3`;
  - verifies scale-transition realization is witness-mediated.

- narrow import wiring into the appropriate cognition/core rollup only after the focused owners compile.

No existing owner should be rewritten unless an import seam is required.

## Data flow

### Cognitive refinement

`continuous hidden oscillator state`

`-> hidden dynamics/update`

`-> stable/invariant learned class`

`-> observation/realisation witness`

`-> MemoryFibre / finite phase-bearing public carrier`

`-> existing learning, decision, action, and provenance machinery`

### Multiscale recursion

`SituatedState_n(state, environment, history)`

`-> Dynamics_n`

`-> Trajectory_n`

`-> PersistentClass_n`

`-> Realisation/Observer_n`

`-> EffectiveObject_(n+1)`

`-> Carrier_(n+1)`

## Invariants and boundaries

The implementation must preserve these claims:

1. `rememberedEvent` identity can remain unchanged while hidden learning coordinates change, consistent with `MemoryFibre`, `LearningAlgebra`, and `FibreLearningDynamics`.
2. Continuous phase is not definitionally `Phase3`.
3. Hidden oscillator mismatch is not definitionally cognitive dissonance.
4. Gradient descent is not definitionally Hebbian plasticity.
5. Phase coherence is not truth or empirical adequacy by definition.
6. Persistent lower-level structure is not next-level semantic identity without a realization witness.
7. A stable structure need not be a fixed-point attractor.
8. No backwards-in-time causation is introduced by target/reference states.
9. The new objective surface does not merge all DASHI energy carriers.

## Testing strategy

TDD order:

1. Add a focused regression that imports the proposed owners and requires the following names before implementation; it must fail first because the owners do not exist.
2. Implement `RecursiveScaleTransitionExact` minimally until its regression portion is green.
3. Extend the regression with oscillator refinement requirements and confirm RED.
4. Implement `ContinuousOscillatorMemoryRefinementExact` using existing `MemoryFibre`, `LearningAlgebra`, `PhaseEnrichedTrit`, and `UnifiedEnergyFunctionalSurface` only by narrow imports.
5. Compile the focused regression with Agda.
6. Run `git diff --check` equivalent validation available to the environment.
7. Attempt a bounded aggregate compile/import check; if the full aggregate exceeds the environment budget, report it as inconclusive rather than promoting success.

## Success criteria

The tranche is complete when:

- the recursive state-space equation is represented as a typed family of scale transitions rather than one universal `F`;
- the oscillator hypothesis is represented as a hidden refinement beneath existing public memory carriers;
- learning/objective/measurement are separated;
- stability is generalized beyond local minima/fixed points;
- all listed non-promotion boundaries are explicit;
- focused Agda regression passes from the exact branch head;
- no claim of empirical neuroscience, quantum implementation, FEP equivalence, or Hebbian identity is made without a future producer/receipt.

## Deferred work

Out of scope for this tranche:

- real/complex-number oscillator numerics inside Agda;
- Python/CUDA simulation producer;
- empirical EEG/MEG fitting;
- CRT projectors on a continuous Hilbert/module carrier;
- proof that a particular gradient rule reduces to Hebbian/Oja/Kuramoto dynamics;
- Levin-specific morphogenesis realization;
- cross-domain claim that one physical energy governs all levels;
- empirical promotion of cognitive dissonance or memory interference claims.
