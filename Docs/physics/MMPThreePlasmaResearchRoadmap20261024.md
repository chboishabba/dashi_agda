# Charged-fermion gravity and three dynamically driven plasma regions: research roadmap
**As of:** 2026-10-24  
**Implementation lane:** draft PR #1248 (`research/mmp-s2-fermion-three-plasma-maxcut-20261024`)  
**Base:** `master`  
**Scope:** physics-first, source-specific Einstein–Maxwell–Dirac / semiclassical test, not an antigravity-device assertion.

## End-to-end scientific question

Can one **globally defined, Hadamard-admissible, charged-fermion quantum state**, on a consistently charged and spin-c equipped two-ended spacetime, generate its own renormalized stress and induced current such that the semiclassical Einstein–Maxwell equations close; and can three separate, internally and/or externally driven plasma/EM regions create a **distinct measurable change to that state or geometry**?

Distinguish:
(1) classical effective-stress metric solution;
(2) Dirac spectrum and regulator-dependent finite state;
(3) renormalized QFT expectation on a prescribed metric;
(4) self-consistent quantum backreaction with global source;
(5) stable traversability in several physical signal channels;
(6) realizable experimental drive, power budget and independent gravity-channel evidence.

Neither finite sign tests nor apparent weight anomalies cross these promotions alone.

## Current baseline (do not duplicate)

- **Geometry / matching:** reduced static Einstein–Maxwell + Polyakov LLL + finite massive S² fermion tower. Exact source-variation angular stress, 4D Ward identity, constraint transport `C'=-Phi'C`, effective two-ended ODE examples, and pressure-zero shell-free Reissner–Nordström matching with `M'=r'E` and `K^t_t(int)-K^t_t(RN)=P/(rr')` on constraint. **No globally defined source-derived fermion state on both exteriors.**
- **Finite QFT donor:** a common finite Wilson–Dirac sea yields static lapse/radius/gauge variations and finite gauge/Hessian checks. Regulator-mass sensitivity is observed. **No local covariant 4D renormalization.**
- **Geometric donor:** pointed S² north/south U1 patch, transition e^{iqφ}, quantized first Chern class, S² spin-c zero-mode index; existing Hopf cocycle in sibling PR #1235. **Pointed, puncture, Pin reflection lift, braid, C3 chart, and physical q are separately typed.**
- **Three-drive donor:** three independent EM/plasma regions and combined space-time C3 Floquet toy; existing full spatial C3 curvature/stress mathematics PR #1215 and braid/Pin/KK PR #1239. **No source-specific quantum-stress actuation model.**
- **Historical claims:** Li–Torr/Podkletnov experiments and nulls are model-/apparatus-specific constraints in PR #1120. Rotating disk ≠ three balls. EM wave–gravity exchange PR #1099 is a different coupling observable. 
- **Exact authority:** MMP original 2018 preprint / 2023 CQG paper for a particular magnetically charged traversable fermion construction; Polyakov, Schwinger and sphere spin-c Dirac spectral theory for the reduction; Sadhukhan's 2026 complementary first-order anomaly/Hall and Schwinger/polarization analyses; Zahn's 2014 locally covariant Dirac renormalization. Preserve original authorship, source dates, hypotheses, independent checks and corrected sources. Nothing here gives evidence for MH370 or a working machine.

## Phases, hard gates, concrete deliverables

### Phase 0 — Reproducible frozen baseline (P0, immediate)
**Deliverables**
- [ ] Vendor the *actually executed* local numerical BVP, spectrum, Floquet, finite Wilson–Dirac, junction and results JSON into the governed PR, or commit regenerated scripts/results with explicit run receipts. Current four committed scripts are narrower than the earlier local ZIP. Do not mark tests as run at PR head until they are.
- [ ] Normalize physical units, charge conventions `q=2eQ`, spin structures, Maxwell kinetic prefactor, renormalization scheme, vacuum subtraction and MMP `r_e, ell`. Make all plots and q sweeps declare dimensionless assumptions and mode truncation.
- [ ] Reference baseline ordinary Einstein–Maxwell, static Brown–Maclay (a comparison only), finite-QFT and MMP source calculations without conflating them.
**Gate:** independent rerun on the exact PR head reproduces q=3 failure, q=12/24 finite-domain candidate results, pressure-zero RN identities, gauge Ward checks, and precision/convergence tables; all outputs carry code hash and constants.
**Failure mode:** symbolic checks pass but numerical scripts are only chat attachments, or C1 junction falsely described as physical quantum matching.

### Phase 1 — One global charged-fermion source `W_ren` (P1, CRITICAL PATH)
**Deliverables**
- [ ] Fix a globally defined spin-c bundle and magnetic flux sector on throat plus two physical mouths, with chosen incoming/outgoing or thermodynamic fermionic state; specify whether the state is static, time dependent, or Keldysh in-in.
- [ ] Separate LLL and higher spherical Dirac modes **without overlap**. Work from 4D Dirac differential operator including sphere spin connection, radial dilaton `r(x)`, EM gauge and boundary holonomies. Recover appropriate MMP limits.
- [ ] Perform covariant Hadamard/point-splitting or heat-kernel-subtracted renormalization with a documented finite local counterterm convention, and demonstrate numerical regulator/mode/cutoff convergence for invariant observables under the fixed scheme.
- [ ] Derive **from the same source** `T_{μν}=(2/sqrt(-g))δW_ren/δg^{μν}`, `J^μ=(1/sqrt(-g))δW_ren/δA_μ` (with sign conventions stated), spherical angular/radion stress, trace anomaly, Hall / Euler and Schwinger/polarization responses, not independent fitted pressures.
- [ ] Prove/verify gauge Ward `∇_μ J^μ=0`; diffeo Ward `∇_μ T^{μ}{}_{ν}=F_{νμ}J^μ` where classical Maxwell exchanges force; Bianchi/source balance; state transition continuity.
**Gate:** a single correctly renormalized, same-state generating functional or equivalent 2-point-function construction computes **all** stress components and currents on a nonconstant reference geometry, with source-derived Ward identities and convergence. Repeat 2026 perturbative donor results at correct scope.
**Explicit unresolved issue:** time-dependent plasma boundary control requires in-in/non-equilibrium state, not one adiabatic static Casimir circumference.

### Phase 2 — Self-consistent two-mouth boundary value (P2, depends P1)
**Deliverables**
- [ ] Coupled Einstein `G_{μν}+Λg_{μν}=8πG(T^EM_{μν}+<T^Dirac_{μν}>_ren)`, Maxwell `∇_μF^{μν}=J^ν`, Dirac-state equations (plus quantum response) on **one** spacetime.
- [ ] Use existing pressure-zero/Misner–Sharp/Israel solution as **initial guess / shooting preconditioner**, not as a source shutoff boundary condition.
- [ ] Solve interior and both mouths jointly; impose charge quantization, Gauss law/topological consistency, correct asymptotic data, no unexplained delta shells, Einstein and Maxwell constraints, finite renormalized energy/counterterm convention and horizon-free two-ended topology.
- [ ] Source/scheme and grid/mode truncation sweeps, residual/interval bounds; measure dependence on `q`, state and circumference and compare MMP physical scaling rather than arbitrary `L=20`.
**Gate:** one global, state-dependent solution with residual convergence **in all components**, no distributional matter-wall artifact, horizon-free throat and admissible asymptotic mouths. Negative ANEC is an output, not a substitute for the source equation.
**Fallback:** if global solve fails, produce a localized no-go under exactly specified state/action and an explicit rank-ordered source of mismatch.

### Phase 3 — Stability, signals, QEI, budgets (P3, depends P2)
**Deliverables**
- [ ] All relevant linearized gravitational/EM/fermionic response sectors incl. `l=0,1` (published `l≥2` stability alone insufficient), mode fluxes, gauge constraints and reasonable nonlinear perturbation test.
- [ ] Null/timelike travel observables and transfer/scattering matrices for scalar, photon and charged fermion, potentially Floquet-engineered channels; conservation, resonance and backreaction of injected signal.
- [ ] QEI/ANEC along relevant complete curves, renormalized stress fluctuations, power/time/size scaling, causality, quantum state preparation and lifetime.
**Gate:** finite physically identified transit channel in an admissible background; no growing modes in the declared range; bounded stress and state-dependent stability/energy budgets. Uncertainty reported, not suppressed.

### Phase 4 — Three independently driven plasma regions (P4, parallel exploratory; must feed P1–P3)
**Deliverables**
- [ ] Specify three 3D field regions `E_i(x,t), B_i(x,t)`, internal/external rotations, field boundaries, mutual coupling, geometry, power, matter currents and conservation; no disk proxy unless independently justified.
- [ ] Construct a causal driven Maxwell–plasma boundary problem with (possibly combined space+time) C3 covariance, and **derive** the actual quantum boundary/holonomy drive in the global Dirac operator or propagator, then its `δ<T_{μν}>` and `δJ_μ`.
- [ ] Reuse pointed gauge sections/Hopf Chern/Pin only with explicit physical bundle morphisms; actual braid clearing and puncture avoidance as needed. For ordinary smooth Maxwell in `R³`, net enclosed monopole charge remains zero. Show whether the proposed system needs a preexisting nonbounding wormhole cycle, magnetic charge, or a completely different non-topological quantum channel.
- [ ] Scan integer q, drive frequency, geometry and symmetry-breaking controls. Treat JMD GF(27) `3+8×3`, GF(2^12), Golay [12,6,6] and Monster `4096×24` as **labelled mathematical donors only** until an explicit operator intertwiner/selection theorem pays a physical role. SUSY/Witten-owner is currently boundary-only.
**Gate:** a controlled three-region drive has a source-derived and distinguishable change in stress/current or transmission relative to a matched nonsymmetric/undriven apparatus. Field rotation alone is not curvature.

### Phase 5 — Measurement and independent physical discrimination (P5, depends physical P4 candidate)
**Deliverables**
- [ ] Separate apparatus weight/thrust from external free-fall, optical/clock, gravito-magnetic and wave channels. Model ordinary EM forces, vibration, thermal flows, sensor pickups, conventional GR and geometry before fitting any residual.
- [ ] Same-apparatus phase-on/off, orientation reversal, time-reversal/chirp, field-frequency sweep, source-probe separation, dummy materials, null C3 drive; blind controls and independent replication.
- [ ] Conservative confidence/upper bound accounting and comparison with Podkletnov, Li–Torr/Kowitt, Hathaway/NASA, Tajmar and Schützhold at their distinct actual apparatus/configuration scopes.
**Gate:** independently reproduced external gravity-channel result with calibrated scaling and ruled-out ordinary-force alternatives; not simply a positive local pressure or Casimir measurement.

### Phase 6 — Optional theory extensions (P6, NOT on critical path)
- KK/radion, Monster/VOA, SUSY/Witten index, Golay/Mathieu, E8, T9/T27 pointed/Pin/puncture and advanced hyperfabric may contribute **if** they supply a nontrivial same-object action, state, source term or measured selection rule missing from P1–P5.
- BIDI against the physical `W_ren`, Maxwell gauge and 4D Einstein consumers. Do not demand that unrelated attractive mathematics be completed before the quantum-state bottleneck is tested.

## Pareto schedule / max-cut

**Next three tasks in order**
1. **P0 exact-head rerun and migrate the actual numerical BVP scripts** into PR #1248. Make q12/q24 two-mouth data independently reproducible; current PR has only a subset of the executed local code.
2. **P1 minimal globally defined fermion state & Ward closure** on the already-calculated nonconstant spherical reference metric. First target: point-split `<T>,<J>` across the pressure-zero region without declaring a state cutoff. Numerical counterterm regulator stability first.
3. **P2 BVP replacement test**: feed this SAME renormalized stress/current to the existing shooting code. Track whether matching pressure remains zero, where charge/current flow, and what the corrected mass, lapse and ANEC become.

**Portfolio allocation (heuristic, not an evidence claim):** ~65% to P1, ~20% to P2 preparatory shooting/convergence, ~10% to plasma-actuator source coupling, ~5% to optional 12/24/VOA/SUSY exploration. P0 is an immediate prerequisite.

## Exact PR-head acceptance commands

```sh
python3 scripts/check_mmp_s2_fermion_source_weld_20261024.py
python3 scripts/check_mmp_israel_rn_junction_20261024.py
python3 scripts/check_pointed_monopole_c3_roles_20261024.py
python3 scripts/check_mmp_static_curved_fermion_same_action_20261024.py
```

These are committed **source-written targets** and are not represented as executed CI or Agda kernel receipts here. Numeric BVP acceptance commands can be elevated to PR-head receipts only after the full companion code/data are committed. The existing archive/chat results are finite calculations, not empirical evidence.

## Phase exit summary

| Phase | Present status | Promote only after |
|---|---|---|
| 0 reproducibility | partial | exact-head independent numerical replay and convention map |
| 1 global W_ren | OPEN — primary bottleneck | one regulated global state with all Ward identities, angular stress and currents |
| 2 self-consistent global solve | classical effective prototype, physical OPEN | same-state full Einstein–Maxwell–Dirac residual, both mouths |
| 3 stable traversal | illustrative channels only | physical state + perturbative/stability/energy tests |
| 4 three-drive coupling | mathematical C3/braid donors only | explicit plasma-to-Dirac source coupling and differential prediction |
| 5 experimentally identified gravity | historical constraints only | replicated external metric/free-fall/phase observable with nuisance exclusion |
| 6 optional unification | disparate donors | same-object measurable or theorem-bearing impact on phases 1–5 |
