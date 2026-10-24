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


## Oct 24 Horned C3 / anomaly max-cut: new physical priority and evidence

**Full source note:** [`Docs/physics/MMPAlexanderHornedC3HelicityPhysicalBidi20261024.md`](MMPAlexanderHornedC3HelicityPhysicalBidi20261024.md). Reuse PR #1244 horned exact finite / three-arm geometry, PR #1235 Hopf, PR #1239 braid/Pin/KK, PR #1215 C3 curvature rather than duplicating. They remain sibling branches and cannot be assumed compiled here.

### Where horns genuinely matter

- Alexander duality on *any* embedded S²⊂S³, even wild, gives two acyclic complementary regions: H1=0, H2=0, H²(Z)=0. This fails the ordinary U1 first-Chern-class flux consumer of spatial R×S² (H₂=Z). **Horned wild complement alone cannot be substituted for magnetically charged MMP throat.**
- Its nontrivial perfect pi1 and PR #1244 finite A5³⋊C3 actor create an **optional non-Abelian holonomy / curved Dirac boundary-spectrum** target. Actual geometric collar/pi1 theorem, an SO3-to-spin/SU2 lift and smooth self-adjoint spectral limit are separate, still open. No physical stress from A5 representation alone.
- Three ordinary 3D balls do not manufacture nontrivial Maxwell monopole charge. The 2D punctured braid, pointed base marker, Pin reflection and true S² flux are NOT identical. Constrained actual magnetic tubes/knotted field lines may introduce helicity, which deserves different physical scrutiny from horn topology.

### The high-value P4 route that can actually source fermion response

An analytic 3D periodic Beltrami model with three independently driven solenoidal field modes has exact
`H=k Vol Σ_i f_i²`, `∫E·B= -(1/2)dH/dt`. For one massless Dirac species (closed volume/no boundary axial flow),
`dQ5/dt = e²/(2pi²)∫E·B`, whence
`d/dt[Q5 + e² H/(4pi²)]=0`.
This is the established ABJ anomaly and Maxwell helicity evolution, **not** new exotic energy production.

- **Negative control:** equal balanced 120° C3 phase rotation `f_i=a cos(ωt+2πi/3)` conserves total H and has zero *integrated* E·B. Rotation alone is NOT a net chiral pump.
- **Constructive but limited response:** slowly or rapidly modulating envelope `u(t)` gives `∫E·B = -(3/2)k Vol uu'`, potentially source-driving chirality and a time-dependent quantum state.
- **Adversarial NEC discriminator:** under one elementary *flat 1+1D continuum chemical-potential approximation* for free Dirac species, the chiral excitation contribution to energy is positive `Δρ=q μ5²/(2pi)` and adds positive `Δ(ρ+p_r)=q μ5²/pi`, weakening rather than improving the negative-NS-vacuum NEC. Threshold `μ5 L=pi/sqrt(3)` is formally algebraic but **not valid as an exact discrete finite-size circle transition**. These modes do not prove a positive or negative net 4D curved-space stress.
- Therefore P4 next step = actual localized 3D plasma Maxwell/MHD response → physical E·B and relative helicity including boundary terms → an **in-in fermion state** → full renormalized stress *change*, not generic rotational-field energy or axial charge alone.

### P0 promotion (executed locally, narrower than full exact-head receipt)

- Added standalone, relative-path-independent `scripts/check_mmp_global_effective_bvp_replay_20261024.py` to PR #1248. Its independently equivalent local executable reproduced q=10,11,12,13,24 two-mouth **effective** geometries and RN Israel no-shell K mismatch within numerical tolerance; q12 R≈11.683162, M≈5.997338, radial ANEC≈-0.000511162. This no longer depends on the separate chat ZIP to replay the numerical BVP at current PR source.
- Added `scripts/check_horned_vs_mmp_magnetic_topology_20261024.py` to check finite Alexander-duality bookkeeping and a concrete A5 perfect/C3 actor (the underlying topology theorem is externally sourced, not established by Python).
- Added `scripts/check_three_drives_helicity_axial_anomaly_20261024.py` for symbolic balanced-null/envelope-source helicity/anomaly identities.
- Added `scripts/check_fermion_axial_pump_nec_budget_20261024.py` for deliberately adversarial sign analysis in the restricted 1+1D free continuum Fock-state model.

**All four corresponding local model checks ran and passed on 2026-10-24.** Actual GitHub exact-head execution / Agda/Lean kernel status is NOT established. Full P0 source/code provenance, mode truncation grid and physical scaling verification remain open. P1 global renormalized state is still the major mathematical bottleneck.

### Updated decisions

1. **Keep P1 global same-state 4D renormalization the primary mathematical critical path.** Do not attempt wild horn geometry before this.
2. **Use exact pressure-zero no-Israel-shell geometry as a P2 numerical preconditioner**, never as proof that a fermion state vanishes naturally at junction.
3. **Advance P4 through helicity/ABJ with a sign-adversarial renormalized null-stress test**, not directly through horn topology or a rotating-disk substitution.
4. **Put horned wild C3 into P6 optional, with a narrow trigger:** physical non-Abelian connection on sourced geometry, actual spin/Dirac bundle, regulator/spectral convergence and a computed stress or transmission difference. Otherwise record the proven no-flux relevance boundary and avoid further expansion.
5. **Preserve attribution:** Alexander 1924/Hatcher; MMP 2018/2023; Adler/Bell-Jackiw 1969; prior MathWorld/Alexander-duality and MHD helicity theory; original JMD/GF content separately. Code-written/locally run ≠ Agda kernel-certified or real apparatus.

### New focused acceptance

```sh
python3 scripts/check_mmp_global_effective_bvp_replay_20261024.py
python3 scripts/check_horned_vs_mmp_magnetic_topology_20261024.py
python3 scripts/check_three_drives_helicity_axial_anomaly_20261024.py
python3 scripts/check_fermion_axial_pump_nec_budget_20261024.py
```


### P4 milestone sharpened — actual three localized field regions

A self-contained local-physics surrogate is now **committed**, `scripts/check_three_localized_field_helicity_20261024.py`: three separate Gaussian twisted vector potentials, exact `div B=0`, positive helicity density, exact cross-helicity integral with independently executed 3D Gauss–Hermite quadrature (≈1.3e-15 agreement). Balanced C3 phase drive has zero integrated anomaly pump even when packets overlap; amplitude envelope creates a nonzero `E·B` source and formally exchanges axial charge with helicity.

**Next required promotion is NOT more C3 numerology:** replace prescribed packets with material-consistent Maxwell–MHD/plasma dynamics (external/internally rotating E,B, real matter current, finite walls, supplied work, surface helicity flux), then compute the *in-in* fermionic `δ<T_kk>_ren` including ordinary Maxwell positive NEC, causal state prep, fermion mass/chirality relaxation and signal backreaction. A positive axial-charge measurement cannot be counted as negative quantum energy. Wild-horn topology remains optional P6.


## New critical-path reassessment, 2026-10-24: global loop quantum state BEFORE full 4D Dirac solve

**See [`MMPGlobalDiracOpticalLoopStateMaxCut20261024.md`](MMPGlobalDiracOpticalLoopStateMaxCut20261024.md).**

A prior constraint has moved ahead of the originally identified P1 renormalization bottleneck: **MMP LLL Casimir energy exists on actual closed magnetic field lines returning through the same external universe**. The earlier model glued RN exteriors independently to each end of `R×S²`. It has an effective C1 Israel solution and negative ANEC but **does not implement the same-universe handle or closed fermion return path**. A radial coordinate pressure zero is *not* an exterior quantum-state boundary condition.

**New P0a global topology/magnetic-loop gate (CRITICAL PATH, not optional horn topology):** build same-asymptotic-universe two-mouth 3D handle schematically `R³#(S¹×S²)` with H1=H2=Z, actual U1 magnetic field lines linking the mouths, spin-c lift, Wilson holonomy and global optical length. A two-ended `R×S²` has H1=0,H2=Z; classical Alexander horn complement has H1=H2=0. Neither is the needed closed-line geometry by itself. The 2026 horned PR #1244 is therefore still optional non-Abelian P6, not the solution to this U1 loop gate.

**New P1a completed at scoped 2D level:** one genuinely global, static, zeta-renormalized massless complex Dirac conformal-circle state with
`E_ren[N,h,α]=2πc B2(α)/(∮ h/N dx) - c/(24π)∮N'²/(hN) dx`.
Its same-state lapse/spatial metric variations produce both anomaly-corrected density and radial pressure; the Wilson phase derivative produces equilibrium persistent current. Symbolic Ward+trace and independent finite variation refinement PASS. The C3 holonomy shift ±1/3 from NS α=1/2 flips B2 from -1/12 to +1/36 IN THIS LOOP MODEL; no three-ball physical holonomy generation is asserted.

**New P0b optical consistency gate:** `L_loop = τ_inside + τ_external_return`, return ≥0. The old `L=20` q=12,13,24 effective numerical solutions FAIL even the nonnegative-return necessary condition. Illustrative q12 model with **assumed** return 2.0 has a conditional optical fixed point `L=22.516301125725`, internal transit 20.516301125718, matched RN radius 12.793819, mass 5.997251, and effective ANEC -3.631e-4. This only solves the length-normalization equation of the existing source; the exterior fermion stress/state and Maxwell field-line geometry remain unsolved.

**New P1b noncompact source no-go:** in a stationary conserved 2D free Dirac conformal state on an asymptotically Minkowski infinite line, chiral t constants must vanish if both asymptotics are vacuum. Patching constant negative Casimir t to zero creates radial Ward defect 2t'/N². For t=0, the 2D null integral of the conformal vacuum is c/(12π)∫F²/N dx ≥0 with decay boundaries. This does NOT exclude the physical MMP closed-loop state; it shows why imposing that state on a different topology cannot be repaired by junction pressure alone.

**New priority order:** (0) existing code reproducibility, (0a) actual closed flux/spin/Wilson loop and optical state; (1a) exact 2D loop current/stress [bounded DONE]; (1b) **full 4D globally Hadamard and covariantly renormalized spin-c Dirac stress/current** [OPEN]; (2) *one-state* Einstein–Maxwell + exterior handle solve [OPEN]; (3) stability and QEI; (4) dynamic three localized source Wilson/helicity response; (6) horned/JMD/SUSY only if a physical operator weld is provided. Preserve MMP original publication and all prior theorem authorship.

Committed acceptance:
```sh
python3 scripts/check_global_dirac_optical_circle_source_20261024.py
python3 scripts/check_mmp_closed_loop_optical_fixedpoint_20261024.py
python3 scripts/check_noncompact_static_dirac_state_nogo_20261024.py
```

These scripts' locally equivalent calculations passed. Neither PR-head CI nor any full 4D Einstein-Maxwell-Dirac quantum saddle is claimed.
