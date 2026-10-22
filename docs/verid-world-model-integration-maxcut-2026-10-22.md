# VERID laboratory/world-model max-cut (2026-10-22)

## Ownership and scope

Google VERID is an empirical laboratory instance, **not** a new semantics or world-model compiler. Canonical owners:

- `DASHI.WorldModel.ActionConditionedWorldModelCore`: action-sequence-conditioned rollout, task/guard energies, selected-action authority and dependency witnesses.
- `DASHI.WorldModel.PredicateNormalWorldModelCore`: observation -> carrier -> PNF -> Phi/Psi -> candidate action -> rollout. Proposals are not truth.
- `DASHI.WorldModel.ActionRolloutPullbackCore`: invalid dependency pulls back a rollout.
- `DASHI.Core.ConsumerFibreRepairExact`: non-descent witness forces separation by any globally sufficient refinement; separating one collision is not global sufficiency.
- `DASHI.Interop.SLRBoundedResearchIterationControlExact`: research iteration transport never creates semantic authority or evidence payment.
- Generic SensibLaw/ITIR world-model compiler: domain-specific evidence as candidate source adapters, not parallel compiler.

## This cut

`VERIDLabWorldModelInstanceExact.agda` makes the missing safety/conformity/evidence obligations explicit *on top of* the existing `SelectedActionSequence`, proves contact inherits live-dependency/closed-authority, reuses canonical proposal and pullback proofs, and demonstrates that the fail-closed fixture cannot promote or dispatch an action.

This is a **formal contract and negative fixture**, not a robot-driver implementation or a claim that physical-lab operations are certified.

## Open empirical contacts

1. Concrete laboratory `State`, `Action`, `Trajectory` values and capacity/material/geometry guards.
2. Simulation refinement or bounded error measured against instrument behaviour.
3. Versioned state snapshot bound to dispatch, with calibration and authorization receipts.
4. Native observation and execution traces through typed SLRW/SLRO/SLRX contracts, respecting the source-vs-observation distinction.
5. End-to-end experiment: safe simulated transfer, unsafe overflow rejection, stale-state rejection and observed post-state reconciliation.
6. Source attribution and result ceilings: VERID demonstration evidence is not general autonomous biological discovery.

## Reproduction

From repository root with the pinned Agda/stdlib environment:

```sh
agda -i . -i /path/to/agda-stdlib/src DASHI/WorldModel/VERIDLabWorldModelInstanceExact.agda
```

Use the repository's Agda 2.9 parallel-check wrapper if available. No kernel receipt is attached to this GitHub-side change; source-writing is not kernel certification.

## Acceptance

- Existing semantic owners unchanged.
- New negative fixture is kernel-checked.
- Positive laboratory fixture only after its concrete safety/refinement/observation receipts exist.
- No generated candidate source, selected route, closed contact gate or simulator output is promoted as physical truth.

## 2026-10-22 proof-search / experiment max-cut

New `DASHI/WorldModel/VERIDExperimentProofSearchBridgeExact.agda` reuses:
- `SequentialConsumerExperimentPlannerExact.SequentialConsumerPlan`;
- `DiscriminatorSynthesisExact.ExperimentBundle` and `DiscriminatingLanguageExtension`;
- `AristotleActiveExperimentalProofSearchLoopExact.initialIteration`;
- `ProofSearchExperimentalParetoCrossPollinationExact` and `ProofExperimentAction369IntegrationExact` authority boundaries;
- the lab contact from the previous cut, with **separate** simulation vs physical safety/conformity/observation payments.

The finite fixture has two Bool worlds with the same coarse observation. The identity experiment bundle distinguishes them, and `extensionJoinSeparates` rules out equality of the joined observations. This is a symbolic regression, not a calibrated laboratory measurement.

**Digital-ESD cross-pollination, without domain conflation:** The `DigitalESDStudyResultPNFProofSearchExact` source's strongest-paid vs first-unpaid implication and study-specific uncertainty ceilings motivate separately recording model-safe, physically observed, and causally identified claims. No educational population effect or statistical estimate is transferred into physical-lab semantics.

**Remaining priorities:** kernel-check the new modules; finite *positive* governed lab instance; concrete state-version/capacity guards; observation-wire receipts; instrument-specific calibration and benchmark against the same experiment planner without typed repair. Do not mark those as complete based on symbolic non-descent or action-gate declarations.

### Suggested check (Agda 2.9 pinned environment)

```sh
AGDA_BIN="$PWD/scripts/agda29_without_k_wrapper.sh" \
  scripts/run_agda29_parallel_check.sh \
  DASHI/WorldModel/VERIDLabWorldModelInstanceExact.agda \
  DASHI/WorldModel/VERIDExperimentProofSearchBridgeExact.agda
```

Kernel receipt: **not yet obtained in this editing environment**.

## Ibrahim / snowball / Pareto max-cut

The new `DASHI/WorldModel/VERIDIbrahimSnowballParetoBridgeExact.agda` makes VERID's first live laboratory consumer a **redirect**, not a closure. It imports the canonical `LiteralFrontierSchedulerExact`, `SnowballAtomWrongTypeScaleInvariantExact`, `ProofSearchExperimentalParetoCrossPollinationExact`, and `IbrahimSnowballParetoFrontierExact` owners rather than copying their algorithms.

- Ibrahim: same-object source identification and non-substitution; the historical first-link corpus is an **acquisition/provenance method** example, not evidence for lab action.
- Snowball: retain source discoveries out of order; payment is receipt- and consumer-relative; first unpaid physical calibration remains open.
- Pareto: rank actionable residual-reducing experiments by declared cost/risk/discrimination, with no automatic promotion from membership in a frontier.
- Literal scheduler: `redirectFrontier` for the symbolic two-world discriminator, not `closeLeaf`; never use a string reference as an execution capability.
- Digital ESD: borrow strongest-paid/first-unpaid claim ceilings, not educational causal conclusions.

### Next executable cut

Build a positive finite model with (1) a concrete capacity/volume invariant, (2) a lab-native stale-snapshot guard, (3) a realized discriminator outcome, (4) version-bound authority and physical evidence separate from formal simulation, and (5) native SLRW/SLRO execution receipt. Benchmark two otherwise identical planners with and without fibre-sensitive experiment selection. Pending Agda kernel checks, all new modules remain source-written only.

## Early DASHItest / DASHIfine / NS cross-pollination

Concrete legacy owners found:
- `DASHI/Programmes/TestHarnessExact.agda`: heterogeneous dashitest experiments attached to shared prediction/inference and kernel-defect contracts.
- `DASHI/Programmes/DashifineExact.agda`: spectral/quotient/operator experiments under receipt-gated inference.
- `DASHI/Programmes/DashifineWaveProjectionFamilyExact.agda`: preregistered three-task (fullXY/xOnly/yOnly) projection stress; one-task success cannot be lifted to family-wide superiority.
- `DASHI/Physics/Closure/NSTriadKNHighestAlphaRound63Exact.agda`: finite Galerkin reality-orbit and coefficient-count repairs; explicitly unpaid physical bounds and continuum producers.

New `VERIDLegacyExperimentProjectionReuseExact.agda` reuses both programme receipts and the projection benchmark boundary, exhibiting a finite coarse-observer collision and discriminating-coordinate repair. This is a negative/projection-invariance stress test, not an NS-to-laboratory physics theorem.

### Highest-alpha physical obligation

State a validated abstraction relation between a real physical transition and the simulated rollout, with an explicitly calibrated error envelope. Then derive a safety-margin transfer under declared Lipschitz/robustness assumptions, preserving time-indexed state versions. Do not import finite NS Galerkin constructions as proof of real-world convergence or calibrated liquid handling.

### Benchmark preregistration

Declare three task variants before evaluation: full state, dropped critical state coordinate, and sensor-noisy state. Compare baseline action selection, discriminator-aware planning and abstention. Measure failure-to-detect dangerous ambiguity, false promotion, experiment/measurement cost, and calibration error. Retain per-task receipts; do not generalize a one-task win.

## 2026-10-22 NS as twin / simulator as experimental system

We reuse the actual numerical solver in `scripts/ns_five_halves_galerkin_trajectory.py` (periodic finite Galerkin RK4; three fixed seeds). New `scripts/ns_verid_simulation_contact.py` runs it with `dt` and `dt/2` at identical horizons and cutoffs, compares final energy, time-integrated weighted five-halves and vorticity Fourier L1 quantities, and produces a deterministic digest and strictly non-promoting authority fields. `tests/test_ns_verid_simulation_contact.py` checks deterministic outputs, matched horizons, negative authority fields, projected-state collision and invalid arguments.

`DASHI/WorldModel/VERIDNSFiniteTwinContactExact.agda` imports the existing finite canonical NS Galerkin RHS mode-retention (Round 65), path-history residue and VERID experiment/frontier owners. The receipt is *not* a proof that the Python numerical RHS is identical to Agda's literal Fourier RHS. That semantic parity remains a named next producer.

Proposed experiment stack:
1. **Formal twin:** exact finite modal coordinates, reality constraint, RHS geometry/invariants, cutoff-indexed obligations.
2. **Numerical experiment:** independently replayable simulation, digest, time grid, observable comparisons; currently two runs of the **same** RK4 solver with different time steps.
3. **Validation model:** separate discretisation error, reference-solver disagreement, state-projection loss and physical model discrepancy. A smaller RK4 step alone does not certify error versus the mathematical ODE.
4. **Physical contact:** calibrated measurements only if/when available; do not substitute simulation traces for real-world experimental evidence.
5. **F1 analogy:** F1 teams use software simulations, wind tunnels, dyno/test rigs, telemetry and track runs iteratively; the useful analogy is model correlation and discrepancy-led design, not an assertion that their measurements establish this specific NS simulation's fidelity.

Run from the repository root with dependencies installed:
```sh
python -m unittest discover -s tests -p 'test_ns_verid_simulation_contact.py'
python scripts/ns_verid_simulation_contact.py --steps 8 --dt 0.002 --output-json /tmp/ns_verid_contact.json
```

No runtime or Agda kernel receipt was obtained in this GitHub connector session. The symbolic projection fixture is preregistered, not a derived performance win. Next highest-alpha action: connect two **independent** solver implementations to one pinned finite same-object initial state and timestep/horizon, then prove/calibrate numerical RHS parity and error envelopes; add matched full/projection/noisy benchmark conditions and held-out physical measurement when possible.

## Cross-integrator numerical contact and revised steelman

`scripts/ns_verid_cross_integrator_contact.py` runs existing finite Fourier Galerkin `rhs` through two *different time integrators*: canonical fixed-step RK4 and adaptive SciPy DOP853. It holds initial seed, cutoff, viscosity and horizon fixed and records energy, five-halves, Fourier vorticity, modal L2 discrepancy and digest. This is stronger than RK4-vs-half-RK4 as a numerical check but both share **the same Fourier RHS and state geometry**. It is neither independently coded spatial-physics validation nor a rigorous numerical error bound. `tests/test_ns_verid_cross_integrator_contact.py` covers determinism, finite discrepancy and authority firewalls.

```sh
python -m unittest discover -s tests -p 'test_ns_verid_cross_integrator_contact.py'
python scripts/ns_verid_cross_integrator_contact.py --output-json /tmp/verid_ns_cross_integrator.json
```

The benchmark deliberately excludes numerical agreement from formal theorem closure and physical-action authorization. The first genuinely valuable independent parity experiment is direct Fourier triad summation versus FFT pseudo-spectral RHS on exactly matching retained modes, normalization, dealiasing and projection; only afterwards compare to the Agda literal coefficient owner. Once that works, run full-observation / erased-coordinate / noisy-observation preregistered cohorts and have the *same live residual* select a discriminating experiment.

### Steelman and gap order

1. **Technical novelty hypothesis:** common consumer-relative residual frontier for proof/acquisition/measurement/simulation/action, but distinct authority for each.
2. **Strongest falsifier:** without consumer-relative repair, an otherwise identical controller is no worse across matched held-out worlds and budgets.
3. **Most decisive physical-math theorem:** calibrated simulator-to-ODE defect envelope plus forward invariant/safety-margin transfer, distinguished from continuum NS.
4. **Cross-instrument contact:** finite solver comparison -> independently coded Fourier RHS -> rigorous defect/error bound -> optional laboratory/physical telemetry.
5. **Causal/scope ceiling:** numerical trajectory replay is not causal identification for a real physical system; experimental interventions still need controls and nuisance accounting.
6. **Pareto discipline:** report domination only over declared feasible moves and declared observable/cost/risk coordinates, not an all-domain optimum.
7. **Stopping/reopening:** progress is a measured reduction of the named consumer residual or a typed redirect; stale source, proof or calibration retracts downstream promotion.

Phases: foundation existing; lab-contact / proof/experiment / snowball/pareto adapters source-written; numerical contact code now source-written; runtime verification and formal/numeric RHS parity open; independent physical fidelity and actual model-guided performance benchmark open.

This tranche was committed by GitHub connector without running Python tests, Agda kernel, CI, or any physical experiment.
