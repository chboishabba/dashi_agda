# Charged-fermion gravity and three dynamically driven plasma regions: research roadmap

## October 25 — Pareto/Ibrahim/Snowball effective BVP source audit

**Source-first/Pareto result:** [new original-root/source-genealogy and dependency ledger](MMPParetoIbrahimSnowballSameStateBVP20261025.md) and [executed Einstein-null/full-interior native BVP acceptance](../../scripts/check_mmp_effective_bvp_radial_same_state_cut_20261025.py). This is a new discriminator for the existing 2026-10-24 `check_mmp_global_effective_bvp_replay_20261024.py` model—not another finite lattice simulator.

**Analytic same-source identity:** `Gkk−8πTkk=C_radial/r²`, where `C_radial` is the canonical reduced BVP radial constraint. **Geometric finite-segment integral** `∫(r/N)Gkk dx=−2[r'/N]` must equal the `8πTkk` integral when the *same* effective BVP solution satisfies Einstein. Local tests q=10/12/24 passed everywhere sampled: maximal radial `C` 5.62e-12/4.27e-12/4.37e-12; maximal Einstein k.k. mismatch 1.22e-13/4.05e-14/1.35e-14; integral source/boundary discrepancies ≲1e-12. Local executed new checker SHA256 `0220035006e4ecfff743625bcc27a9c93422cf118ff961b44ad541d2f96154d2`. No exact-head GitHub workflow or kernel proof. The canonical BVP is not duplicated in the PR.

**New P0 junction smoothness discriminator:** existing sharp-cutoff BVP q=10/12/24 has proper-radial RN junction **C1 residual ~4e−13** (metric and first derivatives matched after clock normalization) but nonzero proper-radial `r''` discontinuities +1.111e−4/+1.037e−4/+1.260e−4 and `(log N)''` discontinuities ~3.77e−6/+5.66e−6/+1.21e−5. This is **not** automatically a thin shell (C1 metric) and not a no-go theorem; it identifies the sharp source cutoff and absent physically smooth 4D field/state matching. The source-directed 2021 BSKR claim → Danielson–Satishchandran–Wald–Weinbaum critique → Konoplya–Zhidenko alternative → Kain 2023 time evolution → Weinbaum 2026 numerical challenge are now a typed adversarial literature graph, separately identified from MMP's quantum Casimir sector. Details / source DOIs and independent roles in [the Ibrahim ledger](MMPParetoIbrahimSnowballSameStateBVP20261025.md). Acceptance checker passes with `python -O`.

**What this closes:** the reduced effective BVP's *interior* radial Einstein identity, not its 4D quantum physical origin. **What it rejects:** a two-ended reflected/spherical RN-junction interior is not already the one-ended `(S1×S2)\{pt}` handle; the exterior shared-mouth topology and field/spin-c glue must be built before claiming a physical same-universe MMP solution.

**Fresh high-alpha independent literature root:** Weinbaum, *Obstructions to traversable wormholes in Einstein-Dirac theory*, PRD 114 084004 (5 Oct 2026), DOI `10.1103/g89c-gqyf`, challenges **classical positive-frequency** Einstein–Dirac models and electromagnetic self-interaction, not MMP's quantized Casimir vacuum. Kontou, *Wormhole Restrictions from Quantum Energy Inequalities*, Universe 10 (2024) 291, DOI `10.3390/universe10070291`, independently constrains MMP with doubled smeared null energy conditions. Topological-censorship root Friedman–Schleich–Witt PRL 71 (1993) and **1995 erratum** retain their independent theorem/correction roles. Gérard–Stoskopf general free Hadamard existence, Zahn covariantly renormalized charged current/stress, Freivogel–Fumagalli–Tomašević (2026 arXiv:2606.12528) conditional scattering are **different** proof obligations, not interchangeable corroboration.

**Updated highest-Pareto path:** P0 same one-ended exterior-mouth/global magnetic bundle → P1 physically selected global charged spin-c Hadamard covariance rather than generic existence → P1 Zahn-type same-state renormalized current/stress plus Kontou QEI → P2 full global Einstein–Maxwell constraints/fixed point → then physical fermionic transmission/three-region plasma. Preserve DOI/arXiv original sources; QID/DDC unknown not guessed; stop unproductive extra finite simulations.


**As of:** 2026-10-24  
**Implementation lane:** draft PR #1248 (`research/mmp-s2-fermion-three-plasma-maxcut-20261024`)  
**Base:** `master`  
**Scope:** physics-first, source-specific Einstein–Maxwell–Dirac / semiclassical test, not an antigravity-device assertion.

## Update — 2026-10-25: coupled finite U(1) backreaction (P0/P4 bridge)

**New owned deliverables:** [finite self-consistent electric-link/Dirac three-port checker](../../scripts/check_mmp_three_port_gauge_backreaction_20261025.py) and [full source and constraint ledger](MMPThreeSourceFiniteGaugeBackreactionMaxCut20261025.md). Unlike our previous three externally **prescribed** electromagnetic link potentials, the new 9-site two-component model solves `i Pdot=[h(theta),P]`, `theta_dot=g²E`, `E_dot=-J+Iext`, and the associated external-source charge equation, with explicit Gauss and energy-work constraints. Three independently timed link-current ports are retained. A second committed [tangent response acceptance](../../scripts/check_mmp_three_port_backreaction_tangent_20261025.py) verifies the **coupled** linearized source derivative against finite differences (quadratic error), linear Gauss, retarded support and three-port superposition. Deliberately omitting fermion backreaction yields a nonzero Gauss violation and is a negative control, not an admissible competing physical model. The resulting coupled-minus-source-only electric response is ~0.003322 in finite model units; locally executed Gauss residual ~4.9e-16, energy-work residual ~2.36e-15, source work +0.0014983.

**Promotion boundary:** neither 1+1D electrostatic field dynamics nor the chosen neutralizing background/externally imposed sources is full 3+1D Maxwell–MHD matter, an actual charged curved 4D Hadamard state, a renormalized Einstein source or a measured gravity effect. Preserve Sanders/Zahn/Cauchy/Hadamard source attribution separately from the original Hebenstreit–Berges–Gelfand (2013) and Kasper–Hebenstreit–Berges (2014) real-time coupled gauge/fermion methods. Work is positive for this fixture, not evidence of NEC violation. Local Python fixture passed; no Agda kernel or exact-head GitHub CI receipt claimed.

**Reordered immediate acceptance:** (1) freeze and rerun the new checker at exact PR SHA; (2) implement continuous spin-c Dirac Cauchy/Møller comparison on the same noncompact magnetic-return geometry and explicitly select a CAR Hadamard state; (3) fix local covariant current/tensor subtraction and Ward/counterterms; (4) couple 3D Maxwell–MHD to the same state and stress and test all Einstein/Maxwell constraints. P3Q dual-rail capacity and optional 12/24/horned/VOA structure remain downstream, with source-specific same-object gates.

## Update — 2026-10-25: 2+1D magnetic plaquette cross-pollination

**Audited owner map and executed finite max-cut:** [2D magnetic-plaquette source + full prior-art ledger](MMP2DMagneticPlaquetteThreePortRepoPriorArtMaxCut20261025.md); [coupled 2D field/fermion checker](../../scripts/check_mmp_three_port_2d_compact_u1_20261025.py); [dynamic gauge/linear response checker](../../scripts/check_mmp_three_port_2d_tangent_20261025.py). Existing generic `CompactLieLatticeGauge`, `MaxwellFiniteExteriorChainStrengthening`, `YangMillsLatticeStressWardSliceConservationExact`, `BalabanSU2PolarizationWardDerived`, MMP driven-relative-Cauchy PR interfaces and AQFT typed remaining obligations remain the canonical repo owners; no duplicate theorem ontology or unwarranted continuum promotion.

**New finite physical surrogate (explicit limits):** periodic 3×3 **two-spatial-dimensional** compact U(1) gauge lattice, nonzero local oriented magnetic plaquette flux and energy, a *same Hamiltonian* 18-dimensional Dirac fermion projector, dynamically induced U(1) link current, three separately timed externally imposed link currents, and dynamically conserved corresponding external charge. This is a step beyond the earlier 1D electric-only coupled model; it is **not** 3D laboratory MHD, physical magnetic-monopole charge, global 4D spin-c field, a wormhole, or a quantum gravity field. No claim of negative ANEC or operational antigravity.

**Local exact-source validation:** `python3 scripts/check_mmp_three_port_2d_compact_u1_20261025.py` and `python3 scripts/check_mmp_three_port_2d_tangent_20261025.py` PASSED in local Python/NumPy/SciPy; Gauss max≈6.05e-16, magnetic energy≈3.318e-4, energy/work residual≈−1.38e-14, nontrivial magnetic-force ablation, induced fermion feedback Gauss-negative-control≈6.53e-4; independent quadratic nonlinear-to-tangent convergence, three-port superposition and dynamic spatial gauge-covariance also pass. See source SHA-256 and full bounded results in the linked ledger. **No GitHub exact-head workflow or Agda/Lean kernel execution claimed.**

**Source attribution:** Hebenstreit–Berges–Gelfand 2013 PRD 87 105006; Kasper–Hebenstreit–Berges 2014 PRD 90 025016; Shi–Xiao–Qin–Fisch 2018 PRE 97 053206 **scalar** QED discretization; Wilson/Kogut–Susskind foundational gauge construction and MMP actual separate 2018/2023 wormhole remain original source owners. The 2D numerical code is a DASHI-specific finite derivative/constraint/ablation application, not a newly discovered physical continuum theorem.

**Max-cut gate order stays physical:** P0 rerun/reproduce and calibrate; P1 selected 4D charged-Dirac Hadamard CAR on same-universe magnetic-return geometry with state/counterterm-derived current and all stress components; P2 source/Einstein/Maxwell fixed point; P3 stability and physical dual-rail scattering; P4 material three-region Maxwell–MHD with source- and boundary-controlled experiment; P5 independent gravity measurement. Extra C3/Monster/horned algebra is explicitly optional absent an actual operator/source weld.

## Update — 2026-10-25: 3D Hodge/Maxwell/four-spinor Dirac source max-cut

**Committed exact-source bounded implementation**: [27-site 3D U(1) Maxwell + 4-spinor Dirac](../../scripts/check_mmp_3d_maxwell_dirac_three_ports_20261025.py), [coupled CAR projector tangent/retarded three-port checks](../../scripts/check_mmp_3d_maxwell_dirac_tangent_20261025.py), and [full original-root, repo-owner, local-evidence and physical boundary report](MMP3DMaxwellDiracThreePortNativePriorArtMaxCut20261025.md). These extend the earlier 1D/2D toy models with 3-dimensional electric links **and magnetic plaquettes**, four-component Clifford alpha/beta and one occupied Dirac state; neither external plasma material nor curved Einstein geometry is implied.

**Exact discrete Hodge and equations**: a periodic 3×3×3 grid with 27 sites, 81 oriented links and 81 faces has incidence `D` and curl `C` with exact integer `DCᵀ=CDᵀ=0`, `rank D=26`, `rank C=52`, 3 harmonic links. Source-current, fermionic CAR evolution, electric and magnetic forces follow the SAME finite energy and temporal gauge, including `rho_ext_dot=D I_ext` for three independently timed external source ports. Derived finite Gauss and energy-work identities are tested, not pasted as source-independent conditions. Earlier coarse RK4 **failed** and was refined to `dt=.004`; local final max Gauss≈4.60e-11, CAR orthonormality≈1.98e-10, energy-work≈3.07e-9, magnetic energy≈5.08e-4. Full driven gauge transform agrees at ~1e-14, magnetic-force/fermion-backreaction ablations are nonzero, and future-source physical-projector control passes. The separate tangent CAR response computes all three source derivatives and matches centered nonlinear differences at two perturbation sizes, with quadratic scaling and Gauss ~2e-16. Reproduced locally with NumPy; **no exact-head GitHub workflow or Agda/Lean kernel certification**.

**Native reuse:** existing `CompactLieLatticeGauge`, `MaxwellFiniteExteriorChainStrengthening`, `YangMillsLatticeStressWardSliceConservationExact`, `BalabanSU2PolarizationWardDerived`, G2 2-cell curvature scope and the prior MMP finite gauge/relative-Cauchy owners remain canonical; their continuum promotion guards are **not** discharged by these numerical tests. The method/literature roots are Wilson/Kogut–Susskind, K. S. Yee (1966), Hebenstreit–Berges–Gelfand (2013), and Kasper–Hebenstreit–Berges (2014), the latter already modeling 3-spatial-dimensional gauge–fermion backreaction. Our 27/81-specific regression is not a novel general physics theorem.

**Phase decision**: P0 3D finite Maxwell/Dirac regression now done at local-Python level. **Stop dimension-hopping**. P1 actual noncompact same-universe spin-c background, selected global 4D Hadamard covariance and renormalized gauge/current/stress including angular components remain unresolved; P2 same-source Einstein and Maxwell global fixed point remains unresolved; P3Q physical source-selected two S² LLL rails, gauge-invariant asymptotic encoding and channel capacity remain unresolved; P4 must solve actual plasma material currents/ion dynamics and boundaries, not merely three prescribed classical link currents; P5 empirical gravity-channel measurement remains unvalidated. Convergence in lattice size, regulator and covariant renormalization must precede any physical promotion.

## Oct 25 2026: P1/P2 same-source product no-go and actual curved null geometry

**New most informative physics acceptance:** [restricted one-source Einstein-null / Maxwell-Wilson-current obstruction](../../scripts/check_mmp_product_same_source_einstein_maxwell_obstruction_20261025.py), [independently computed 4D warped Einstein-null identity](../../scripts/check_mmp_warped_null_curvature_identity_20261025.py), [full original-attributed source ledger and assumptions](MMPSameSourceProductNullCurrentObstructionMaxCut20261025.md).

The **constant-radius ultrastatic** `S1×S2` kinematic state is now rejected as a self-consistent Einstein–Maxwell–ideal massless-LLL background for every nonzero monopole index `q` in the **declared restricted sector**: `G_kk=0`, magnetic Maxwell `T_kk=0`, while `T_kk,LLL∝B2(alpha)`. At the only Wilson-phase stationary point `B2'(alpha)=0`, `B2(1/2)=-1/12`; at `B2(alpha)=0` the phase-induced persistent current is nonzero, contradicting the purely magnetic static Maxwell equation. The same energy determines both stress and current. This is NOT a no-go for MMP's nonconstant throat or additional 4D modes/counterterms; cosmological constant alone does not alter the radial null contraction.

The independent full symbolic metric calculation verifies for `ds²=-N(x)²dt²+dx²+r(x)²dΩ²` the exact `G_kk=2[(N'/N)r'-r'']/r`, and at a flaring throat `r'=0,r''>0` obtains negative `G_kk`. Thus P1/P2 must use the **same globally selected nonconstant geometry** rather than a constant-radius circle×sphere proxy. This is an upstream rejection constraint, not a quantum matter solution.

**Prior-art reuse:** native Wilson/Hadamard source bridge, local optical-circle state functional, 4D Einstein tensor and finite Maxwell Hodge/charge obligations; original MMP 2018/2023 (actual wormhole), Zahn (charged Dirac locally covariant renormalization), established massless fermion Casimir. Also repaired four malformed `//` comments in `MMPWilsonHadamardSameBackgroundBidiExact.agda` to parse-compatible `--`; no Agda or Lean kernel/CI claim.

**Revised Pareto:** stop generic finite lattice dimensional escalation (1D→2D→3D already accomplished); spend the primary effort on P1 same noncompact handle spin-c Hadamard state, complete covariant 4D stress and current, and P2 global Einstein+Maxwell constraints. The new scripts are source-written PR acceptance; independent expanded local symbolic prototypes passed, **not** exact-PR-head execution.

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


## 2026-10-24 quantum teleportation / information-transfer cross-pollination (new P3Q)

**Source and implementation:** [`MMPQuantumTeleportationChannelCrossPollination20261024.md`](MMPQuantumTeleportationChannelCrossPollination20261024.md). Previous DASHI teleportation obligations are ALREADY owned by sibling PR #1163: `CausalTransportFTLObligationsExact` and `CausalTransport2026SourceAtlasExact`. TPS/input/output structure has separate proof owner #1128, and 100-spatial-channel optics is the independent published Lou et al. 2026 PRL 137 080801 experiment. Gao–Jafferis–Wall 2016/2017 and Maldacena–Stanford–Yang 2017 are **holographic traversability/teleportation donors**, distinct from Maldacena–Milekhin–Popov 4D charged-fermion wormholes.

**New computed selected finite channel, not an assumed wormhole one:** use the SAME finite Wilson–Dirac Hamiltonian skeleton as PR #1248, choose explicit 2-spinor input/output site subspaces, and project `K=Pout exp(-iHt) Pin`. A CPTP erasure completion is provided by `I-K†K≥0`, with gauge-covariant K and positive Choi. Local expanded numerical fixture PASS (12 sites, q12, best time 12.52 over stated 0–30 scan, mean spin-qubit success ~0.210412, accepted-output ideal-corrected entanglement fidelity ~0.976177, weighted fidelity ~0.205399). **Not** a physically normalized asymptotic 4D wormhole scattering experiment, capacity measurement, or causal front-speed theorem. The reduced committed checker `scripts/check_mmp_teleportation_channel_bridge_20261024.py` requires an independent exact-head run.

**Separate Bell LOCC comparison:** resource Bell pair, Bell measurement with 1/4 each of four outcomes, Bob pre-classical-message I/2, then two classical bits and Pauli correction; expanded local script recovers four tested states at machine precision. This does NOT move the source particle through a wormhole, provide FTL communication, or generate exotic gravitational energy. QET likewise remains separate.

**Add P3Q gates:** (i) select physical encoding/TPS with matching observable same object; (ii) compute flux-normalized 4D in/out Dirac scattering or causal Green function on the P1/P2 *same-state* geometry; (iii) channel Choi/gauge/CPTP, transmission-vs-fidelity-vs-erasure, qubit and optional multimode covariance; (iv) signal front time, injected probe backreaction, charged-current conservation; (v) infer physical C3 drive change only after Maxwell/plasma source determines `δW_ren`, `δS`, `δF`. This phase depends on P1/P2 for a PHYSICAL claim, but source-free finite-channel validation can proceed in parallel. Horned nonabelian topology, Monster and 12/24 counts are not relevant without a true same-operator weld.

**Pareto update:** the single most useful next physical inference is to compute a state-consistent 4D retarded *fermion* response/mode scattering from the GLOBAL magnetic loop and self-consistent metric, then report **both** quantum channel loss and fidelity with physically identifiable endpoints. Do not promote holographic wormhole teleportation or external LOCC experiments to MMP geometry by analogy.


## Oct 24 P3Q continuum current-flux max-cut — new deliverables and corrected clock

**Implementation/source report:** [`MMPDiracFluxScatteringQuantumChannelMaxCut20261024.md`](MMPDiracFluxScatteringQuantumChannelMaxCut20261024.md). The arbitrary finite Wilson–Dirac site transfer benchmark is now supplemented by a **stationary current-normalized reduced continuum Dirac S-matrix** on the *same effective shooting geometry*; these are distinct test objects, so the earlier ~21% finite-lattice transfer must NOT be compared to the new energy-dependent `T(E)` as if they measured the same apparatus.

**P0 improvement DONE as source:** `check_mmp_global_effective_bvp_replay_20261024.py` now exposes an optional `run(q,L,with_profile=True)` returning its dense ODE trajectory and lapse normalization to RN infinity; existing default call semantics are preserved. `check_mmp_dirac_flux_scattering_20261024.py` imports this profile, constructs optical z, `V_n=N sqrt(n(n+|q|))/r`, exact 2×2 Dirac transfer exponentials, current-unitary R/T, U1 open-path gauge test and physically explicit two-mode CPTP erasure selection. `check_mmp_dirac_scattering_precision_20261024.py` separates discretization from cutoff. Existing Bell LOCC and causal transport atlas #1163 are reused, not overwritten.

**Clock conversion critical correction:** q=12, L=22.5163011 input uses throat-local t, but asymptotic-RN-normalized lapse scaling `λ=0.0139837728724`. Physical (in this dimensionless effective geometry) direct interior optical time = `20.5163011/λ=1467.150626`, *not* 20.5163. A hypothetical exterior return 2 in throat units would be 143.022918 in asymptotic time, and total circle 1610.173544. The previous conditional optical root remains a coordinate-covariant normalization equation **only if the exterior return is converted with the same time choice**. There is still no actual same-universe 4D magnetic return path.

**Energy/current channel results (cutoff radius 240, NOT infinity; flux-normalized local-mass endpoint leads):** n=0 LLL exact static massless reflectionless; E=.20: massive n1 T=.9998653, n2 T=3.4463×10^-5, selected n1/n2 mean success η=.4999499, ideal conditional entanglement fidelity ≈.5058707, with state-dependent erasure; E=.55: n1 T=.999999994, n2 T=.999999997, η≈.999999995, conditional fidelity ≈1; E=1: both ≈1 within finite numerical precision. J-unitarity and analytic massive barrier benchmark pass. These are dimensionless fixed-background single-particle predictions from the **effective, artificially cut-off source**, not MMP original full geometry. The assumed two-mode qubit remains a selected mathematical encoding without sourced physical preparation/detection.

**Precision and external-tail gate OPEN:** second-order cell-width refinement at cutoff240, n2 E=.55 with locally massive endpoints gives T=.9999999968138/.9999999967746/.9999999967638 for step .30/.15/.075. RN outer cutoff E=.20 n1 gives T=.99982692 (R=120), .99986528 (R=240), .99985399 (R=480); n2 gives (3.4642,3.4463,3.4478)×10^-5. PREVIOUS massless-at-finite-cutoff spinor boundary numbers were an artificial mismatch, and are retained in the report only for provenance. Do not claim full `R∞` S-matrix convergence. A long-range asymptotic mode prescription and physical same-universe source are still prerequisites.

**Causality:** static reduced Dirac principal characteristics travel at unit optical speed; a stationary transmission/phase/group delay number is NOT a signal-front/FTL receipt. No known theory or local numerical channel test substitutes for physical closed paths, full 4D covariant Dirac renormalization and quantum backreaction.

**Next Pareto three cuts:** (1) exact-head reproducible S-matrix cutoff/grid tests and quantify long-range tail; (2) full 4D spin-c return path/state/point-split Wren and `<T>,<J>` from one source; (3) flux-normalized 4D scattering/channel on the **same physical** solution, with packet causality, detector/TPS, spin and gauge holonomy and three-plasma control. Horned nonabelian topology and generic ER=EPR analogies remain optional; q12 and q24 counts are not a source of quantum channel capacity.

Acceptance:
```sh
python3 scripts/check_mmp_dirac_flux_scattering_20261024.py
python3 scripts/check_mmp_dirac_scattering_precision_20261024.py
```

Local expanded equivalents executed PASS. No current GitHub exact-head CI or Agda/Lean certification claimed.


**Physical boundary correction:** the finite RN radial boundary has nonzero local reduced Dirac mass even though the true limit is massless as R→∞. Match to *unit-current massive lead eigenvectors* at finite radius to avoid fabricated cutoff reflection. The corrected tests were executed locally and supersede the preliminary massless-lead values. This is still a finite-radius adiabatic/Jost approximation, not a rigorous infinity scattering limit; same-universe loop and global 4D state remain open. See [MMPDiracFluxScatteringQuantumChannelMaxCut20261024.md](MMPDiracFluxScatteringQuantumChannelMaxCut20261024.md).


## 2026-10-24 dashi_lean4 source audit and P3Q formal-encoding max-cut

**New cross-repo owners:** dashi_lean4 merged #37 (concrete complex Majorana CAR / even-parity `|00>,|11>` qubit), merged #61/#76 (same-global-state finite-marginal, partial-trace associativity and g-TPS HS projectors), open #68 (corrected Schmidt-cut RT and flat-vacuum Jacobson, not source-identified with MMP), open #80/#84 (TOE/physical provenance and source-owner cut), and **new draft dashi_lean4 #85** (fermionic-loss parity false herald and U1 charge-superselection). See [full sourced discriminator](MMPLeanFockParityQuantumSourceCrossPollination20261024.md).

**P3Q binding correction:** The preexisting q12 scattering matrix `diag(t1,t2)` is a **single-particle, fixed-charge angular-mode qubit**, while Lean #37's even parity code is a **two-complex-fermion Fock occupation logical qubit** `|00>,|11>`. Their transmission probabilities, erasure/accepted outcomes, and gauge superselection differ. For independent fermionic attenuations, strict no-environment-loss Fock success `(1+T1*T2)/2`, parity-only accepted `(1+T1*T2+(1-T1)(1-T2))/2`; false success `(1-T1)(1-T2)/2`, exact source-written Lean algebra plus executed finite Fock Kraus/Choi model. A parity-only receiver *cannot* conclude no loss from an even output, and a single charged Dirac mode is not automatically an experimentally manipulable Majorana zero mode.

**P3Q gauge-charge stronger discriminator:** The parity-code basis |00>,|11> differs in **ordinary electromagnetic U1 charge by 2** if both modes are ordinary charge-1 Dirac fermions. Without a physical reference/dressing, global U1 half-turn phase twirling removes that coherence; fixed-charge dual rail |10>,|01> retains it. Actual source references: Schuch–Verstraete–Cirac PRL 92 (2004) 087904 DOI 10.1103/PhysRevLett.92.087904 and Bartlett–Rudolph–Spekkens RMP 79 (2007) 555 DOI 10.1103/RevModPhys.79.555. A superconducting condensate/charge reference or a gauge-invariant larger relational state could pay the missing bridge but is NOT implicitly supplied by MMP 4D number-conserving Einstein–Maxwell–Dirac.

**Default decision:** select one-particle **equal-charge** dual-rail as first physical quantum channel to attempt; treat Majorana parity code as a distinct optional mathematical consumer requiring charge reference, explicit second quantization, environment no-loss readout, and same-source physical fermion modes. Do not conflate high conditional fidelity with successful transfer, even output parity with survival, or mathematical RT entropy with a Lorentzian physical wormhole.

**Executed local receipt:** `/mnt/data/check_mmp_fock_parity_channel_20261024.py` PASS 4×4 Fock, 3×2 logical/erasure Choi and probability conservation; q12 E=.20 R240 gives false parity-only acceptance 6.7358×10^-5; adversarial T1=.2,T2=.7 gives 0.12; total loss example accepts even parity with probability 1 while single-particle transmission is zero. `/mnt/data/check_mmp_charge_superselection_20261024.py` PASS phase twirl, relative charge, purity. Agda source-written acceptance:
```sh
python3 scripts/check_mmp_lean_fock_parity_channel_20261024.py
python3 scripts/check_mmp_charge_sector_coherence_20261024.py
```
Lean #85 source-written theorem targets:
```sh
lake env lean QuantumChannels/MMPDiracFockParityChannel.lean
lake env lean QuantumChannels/MMPDiracChargeSuperselection.lean
lake env lean QuantumChannels/MMPDiracFockParityChannelRegression.lean
```
No Lean binary installed and no pinned exact-head kernel/CI receipt yet. **Main P1/P2 full global 4D fermion state/Einstein–Maxwell–Dirac fixed point remains OPEN.**


## SOTA/Pareto recut as of October 24 2026: global Hadamard, 2026 QI capacity and LLL rails

**Direct source and tested result:** [`MMP2026SOTAFermionHadamardDualRailCapacitySnowball20261024.md`](MMP2026SOTAFermionHadamardDualRailCapacitySnowball20261024.md). This is the accountable original-root/snowball ledger and distinguishes MMP 2018/2023 original paper family, MMP-specific Freivogel–Fumagalli–Tomašević (2026) scattering and Sadhukhan (2026) linear Hall/anomaly descendants, *versus* GJW/MSY and Lu–Yang–Zheng (PRD **accepted 22 October 2026**) holographic OTOC/capacity lineage, and Bennett–DiVincenzo–Smolin 1997 original erasure capacity lineage. Do not promote paper reprints, analogies or finite toy operators into independent proof receipts.

**P1 physical Hadamard source critical path sharpened:** Capoferri–Murro (2025, DOI 10.1002/mana.12032) give global microlocal Dirac propagator and Hadamard quasifree covariances under a **Cauchy-compact globally hyperbolic 4-manifold** premise. Our single-universe magnetic handle/exterior is not automatically Cauchy compact; pay the noncompact extension/asymptotic microlocal admissibility or use another source with appropriate hypotheses. Zahn (2014) provides charged locally covariant renormalization/conserved current/stress/finite ambiguity; a 2026 spinor heat-kernel/effective-action source pays local counterterm methodology, **not** a global state. P2 quantum fixed point requires same-state nonlocal 4D stress and actual Maxwell field-line return. Kanai–Maeda–Yoshida (2026) restricted perturbative higher-derivative EFT near-horizon no-go does NOT refute sourced Casimir MMP solution.

**P3Q default rail promotion:** use two independently addressable, equal-electric-charge spin-c `S²` LLL *zero modes* `q>=2`, not two arbitrarily selected massive modes `n=1,n=2` unless needed as adversarial control. The `|q|` index multiplicity is established external sphere-Dirac theorem; Lean #85 `MMPMonopoleLLLDualRailCapacity.lean` now constructs two finite mode LABELS conditional on q>=2 and proves exact balanced-erasure threshold algebra. It neither constructs physical wavefunctions nor 4D spin/charge scattering. This shows **q=12/24 is not preferential** for qubit dimension; large physical q may still be needed to control semiclassical throat.

**P3Q receiver + environment source rather than fidelity alone:** newly committed `check_mmp_dualrail_coherent_information_20261024.py` constructs one fixed-charge Stinespring isometry into two fermion rails/vacuum receiver and loss-mode environment, checks CPTP/Choi and complementary partial traces, computes `I_c(I/2)=S(B)-S(E)` from exact same-state spectra. q12 old effective massive n1/n2 at E=.20 yields I_c≈−0.000683 bits; E=.55 gives ≈+0.999999991 bits; two ideal LLL rails yield +1 bit (all conditional on model). For equal T, **external** erasure theorem gives Q=max(0,2T−1) bits/use, but unequal-loss I_c of a selected input is NOT optimized capacity. New `check_mmp_dualrail_erasure_degradability_20261024.py` explicitly constructs CPTP degrade/antidegrade maps across T=1/2; the local fixtures PASS.

**SOTA Gaussian nonpromotion:** Negari–Salek PRL 137 080201 (2026) provide an antidegradability SDP and Gaussian extendibility/entanglement-breaking classification. The selected fixed-charge 3-output erasure channel is NOT automatically their general fermionic Gaussian channel under the same algebra, so no Gaussian classification is inherited without an actual Gaussian representation/physical source map.

**Immediate max-cut:** (1) exact-head replay of new committed Python scripts and Lean #85 (no tools to run kernel here); (2) *global actual four-dimensional Hadamard/renormalized charged-Dirac state on one-universe return-path geometry* and Ward source closure, applying correct microlocal assumptions; (3) backreacted Einstein–Maxwell fixed point; (4) full same-object LLL retarded/LSZ transport plus receiver/environment coherent information and timed signal; (5) sourced three physical plasma EM/MHD drive control. Do not divert to new generic topology/TOE numerology or transplant holographic OTOC capacity to MMP.

Acceptance:
```sh
python3 scripts/check_mmp_dualrail_coherent_information_20261024.py
python3 scripts/check_mmp_dualrail_erasure_degradability_20261024.py
lake env lean QuantumChannels/MMPMonopoleLLLDualRailCapacity.lean  # separate Lean #85 branch
```
No exact-head CI/Lean kernel or 4D semiclassical state solution is claimed in this round.


## 2026-10-24 Cauchy prior-art/max-cut REVISION — resolves over-broad P1 blocker

**Canonical in-repo audit, theorem lineage and executable fixtures:** [`MMPCauchyPriorArtNoncompactDiracThomHandleMaxCut20261024.md`](MMPCauchyPriorArtNoncompactDiracThomHandleMaxCut20261024.md). Users correctly pointed out the extensive existing DASHI Cauchy stack; it should not be reimplemented.

**Do not conflate types:** `Geometry/LCP/Cauchy`, `Analysis/BishopFastCauchyCommonCompletion` and `CarrierSchwingerFunctionCauchyReceipt` handle sequence/field approximation convergence. `Physics/Gravity/PenroseGlobalCausalityAuthorityExact` and `PenroseGlobalHorismosContradictionExact` (merged #898, follow-up #905) own Lorentzian noncompact **Cauchy hypersurface/global hyperbolicity** roles, but source-authority theorem coordinates are NOT locally re-proved continuum geometry. `Physics/QFT/AQFTCarrierAlgebraQuotientSurface` owns an explicitly **open** full Cauchy time-slice algebra isomorphism, not an already proved QFT state.

**Source-paid P0 geometric existence (not Einstein equations):** on `Sigma=(S1×S2)\{pt} ≅ R3#(S1×S2)`, one-ended noncompact `H1=H2=Z`; construct complete asymptotically Euclidean Riemannian `h` via smooth core/exterior collar gluing, then `g=-dt²+h` is globally hyperbolic with each `t=const` a noncompact Cauchy hypersurface (standard ultrastatic complete-slice theorem). On a tubular S1×D2 neighbourhood of the core loop, choose `F=c_q exp[-1/(1-r²)] dx∧dy` with smooth zero extension, normalized to `∫S²F/(2π)=q`, `dF=0`. Its magnetic field runs along **closed return orbits** in a local product metric. Standard Poincaré duality, de Rham/Thom and Misner–Wheeler 1957 retain mathematical/scientific authorship. This is a **true same-universe topology/flux model**, not a Maxwell `d*F=J` or Einstein/fermion backreaction solution, and has NOT been identified with the older C1 two-RN-exterior numerical geometry.

**P0 local noncompact-Cauchy evolution hurdle partly closed at source level:** Capoferri–Murro *Math. Nachr.* 298 (2025) Remark **3.8(2)** explicitly uses smooth spatial collar **doubling** of the compact finite-time causal hull of compactly supported noncompact-Cauchy Dirac data, finite propagation and uniqueness, to reduce it to a compact-Cauchy Cauchy problem on bounded time windows. Its theorem does **not** apply directly to global nonlocal vacuum/Casimir loop correlations. New `MMPDiracCauchyNoncompactCompactDoubleBidiExact.agda` REUSES actual source owners and composes local-data matching plus uniqueness into a conditional same-observable finite-time result. `check_mmp_cauchy_compact_doubling_20261024.py` has a locally executed 1+1D exact chiral propagation fixture: max same-collar local solution / finite-rank kernel error 0 for R10,a1.6,b2.4,|t|≤5, and outside-diamond seam wrap produces mismatch 0.367879. No 4D physical field is asserted.

**P1 EXISTENCE vs SELECTED STATE corrected:** Gérard–Stoskopf *Rev. Math. Phys.* 34 (2022) 2250008, DOI 10.1142/S0129055X22500088, gives general **free** Dirac Hadamard existence on arbitrary globally hyperbolic spin spacetimes and pure constructive methods under bounded-geometry hypotheses. Thus 'compact Cauchy is an existential barrier' is **retired**. Exact applicability to the physically selected charged/twisted spin-c connection and, critically, to a **global NS/Casimir fermion loop state with necessary negative stress** remains OPEN. Zahn 2014 pays external local renormalized current/stress framework; do not treat existence of SOME Hadamard state as existence of the desired semiclassical solution.

**Updated irreducible P1/P2 chain:** select an explicit complete/asymptotically flat **same** spin-c/gauge-twisted handle geometry, prove actual charged Dirac Cauchy propagation and selected CAR/Hadamard covariance with global closed-loop Wilson holonomy; compute SAME-state renormalized `<T>,<J>` including gauge/diffeomorphism Ward and finite counterterm prescription; satisfy **both** Maxwell `dF=0,d*F=*J` and Einstein `G=8πG(T_EM+<T>_ren)` on that selected metric. A source-paid global existence theorem is not a numerical value or negative energy estimate.

**New executed local cut:** `check_mmp_cauchy_handle_thom_flux_20261024.py` numerically checks CW H1/H2, Thom magnetic flux for q0,1,2,12,24,-3 and closed S1 fieldline family; direct analytic support `dF=0`, q12 Chern ≈11.99999999999994. Underlying topology and complete-metric/global-hyperbolic theorems are EXTERNAL original mathematical prior art, not code-generated proofs.

Acceptance:
```sh
python3 scripts/check_mmp_cauchy_compact_doubling_20261024.py
python3 scripts/check_mmp_cauchy_handle_thom_flux_20261024.py
# Optional after selecting actual Agda project library:
agda -i . DASHI/Physics/QFT/MMPDiracCauchyNoncompactCompactDoubleBidiExact.agda
```
No exact-head GitHub workflow, Agda kernel, globally Hadamard charged source, Einstein–Maxwell fixed point or real plasma device is claimed.


**Additional q/holonomy/NS critical discriminator (same noncompact Cauchy handle):** `H¹(Sigma;Z₂)=Z₂` provides two spin structures along the S¹ handle generator, `H¹(Sigma;U1)=U1` supplies variable flat Wilson phase and `H²(Sigma;Z)=Z` independently fixes magnetic flux q. Exact q does NOT fix the full loop fermion boundary condition. New `check_mmp_cauchy_handle_thom_flux_20261024.py` computes Bernoulli `B₂(α_spin+α_Wilson)` for q=2,12,24: NS α=.5 gives negative -1/12, ±1/3 holonomy gives positive +1/36, independent of q. The loop Casimir energy is still a SOURCE-specific 2D approximation; the true 4D charged-fermion spin-c wavefunctions and negative stress are NOT constructed. An actual three-region plasma drive would need to source `δα_Wilson`, not merely a different B or magnetic helicity.


## Wilson + microlocal Hadamard prior art/source-first crosspollination (2026-10-24; replaces erroneous greenfield Wilson gate)

**Proof-owner audit:** [`MMPWilsonHadamardNativePriorArtStateDifferenceMaxCut20261024.md`](MMPWilsonHadamardNativePriorArtStateDifferenceMaxCut20261024.md). The EXISTING `Physics/YangMills/CompactLieLatticeGauge.agda` already proves exact `holonomyGaugeCovariant` for endpoint-indexed open paths and `loopObservableGaugeInvariant` for class functions. The actual Balaban periodic source, `SUNWilsonClassFunction` and `SUNWilsonReflectionPositivity` must be kept in their own types; finite OS positivity is NOT a Lorentzian Hadamard two-point WF. `Analysis/NonArchimedeanHadamardTwistedSectorBidiExact` and Golay Hadamard are MATRIX/CHARACTER identities, not quantum state admissibility. `Physics/QuantumVacuum/CasimirResidualCauchyToLimitExact` already gives a renormalized-limit *consumer given a Cauchy residual*, while explicitly recording the source residual Cauchy estimate as OPEN. `Physics/QFT/AQFTCarrierAlgebraQuotientSurface` still has no actual CAR time-slice isomorphism. Avoid duplicating or promoting any.

**New actual reuse:** `Physics/QFT/MMPWilsonHadamardSameBackgroundBidiExact.agda` imports the actual Wilson group/path theorem, `CompactLieGroupDerived.gaugeTelescope`, existing noncompact Cauchy/QFT owner, AQFT time-slice target and physical Casimir Cauchy-to-limit sequence owner. It proves only conditional relative-group cancellation and separates matrix Hadamard from microlocal Hadamard state. Its arbitrary abstract two-point requirements are not a constructed physical field. Source-written Agda, no kernel CI claim.

**Numerically completed bounded SAME-BACKGROUND state comparison:** `check_mmp_wilson_hadamard_smooth_state_difference_20261024.py` and `check_mmp_wilson_hadamard_cauchy_car_20261024.py` are committed source checkers; independent expanded local tests PASSED. Fixed U1 Wilson fraction β=.17, spin s=.5, n=1/3 extra modes: rank-two smooth two-point difference, Wilson-dressed gauge covariance ~1.1e−16, current difference gauge covariance ~2.2e−16. Complete 61-mode finite CAR reference and excited-state projectors: positivity, CAR complement, idempotence and unitary same-background Cauchy evolution error ~1.6e−16. Individual bare reference-vacuum energy diverges as cutoff increases, but MATCHED reference state difference remains 4.18280621878 in toy units across cutoffs 8/20/64/200. This is a relative-state finite-mode toy, not a 4D renormalized absolute stress.

**Mathematical SOTA authority:** Radzikowski 1996 and Sahlmann–Verch 2001 microlocal Hadamard; Gérard–Stoskopf 2022 and Capoferri–Murro 2025 existence/Dirac evolution; Zahn 2014 charged Dirac point-split counterterms; Michał Wrochna 2012 static external-potential Dirac Hadamard; Shokoufe Faraji Wilson review first published **10 October 2026** DOI 10.1002/prop.70156 (not the original Wilson theorem); Wilson 1974 primary loop heritage; original Maldacena–Milekhin–Popov 2018/2023 magnetic return and negative Casimir physics. DASHI earns only its actual proof/adaptation/numerics, not theorem authorship.

**Sharper genuine P1 target:** On one ACTUAL `(M,g,L,A,s)` charged spin-c background construct a positive quasifree CAR two-point **Hadamard bisolution** `Λ0` with the required WF set and spin/gauge transport; choose a physically sourced loop state `Λ1`. For SAME operator, `Λ1−Λ0` is SMOOTH, so common local parametrix cancels in `Δ<T>,Δ<J>` after correct gauge-covariant point-splitting (existing literature result). This allows efficient *relative* state excitations once absolute reference is constructed. The physical source still needs absolute `<T>_ren`, `<J>_ren`, finite counterterm and consistent Einstein/Maxwell equations.

**MOST IMPORTANT physics no-go/promotion:** three independently dynamic plasma regions generally change `A(t,x)` and perhaps `g`. Different Dirac operators do **not** share a literal common Hadamard parametrix; naive subtraction across backgrounds is unjustified. Must construct a charged spinor-bundle Møller/relative Cauchy evolution (or in-in Schwinger–Keldysh source identification), causal retarded response, background Ward identities and matching local counterterms before claiming `δ<T_kk>`, Wilson transport/fidelity change or an engineered wormhole. Native lattice Wilson covariance DOES NOT PAY this dynamically varying-background gate.

Acceptance:
```sh
python3 scripts/check_mmp_wilson_hadamard_smooth_state_difference_20261024.py
python3 scripts/check_mmp_wilson_hadamard_cauchy_car_20261024.py
# Agda source consumer, when configured (not kernel checked here):
agda -i . DASHI/Physics/QFT/MMPWilsonHadamardSameBackgroundBidiExact.agda
```
No physical Hadamard state, charged renormalized Einstein–Maxwell–Dirac full solution, or source-plasma quantum response was generated by this bounded max-cut.


## 2026-10-25 P1c/P4 causal *changing-background* source max-cut

**Exact original-root ledger, equations, and numeric receipts:** [`MMPDrivenDiracRelativeCauchyPlasmaSourceMaxCut20261025.md`](MMPDrivenDiracRelativeCauchyPlasmaSourceMaxCut20261025.md).

The previous same-background Wilson/Hadamard smooth-state comparison was mathematically useful but CANNOT be reused as a literal parametrix subtraction between two DIFFERENT electromagnetic backgrounds. New authoritative donor: **Ko Sanders** `The locally covariant Dirac field` (2009/2010 arXiv:0911.1304) relates relative Cauchy evolution of the covariant Dirac field to stress commutators; **Jochen Zahn** 2014 charged Dirac renormalization and 2015 `Locally covariant charged fields and background independence` DOI `10.1142/S0129055X15500178` treats perturbative agreement and gauge background dependence. **Finster–Murro–Röken** 2015 arXiv:1501.05522 gives a time-dependent external potential Minkowski *Hadamard* construction only under specified bounds. **Fewster–Schenkel** 2014/2015 external-source RCE is an INHOMOGENEOUS KLEIN-GORDON original, not the charged Dirac theorem. All original physics authority stays with named authors.

**P0 finite algebra DONE (source written):** `DASHI/Physics/QFT/MMPDrivenRelativeWilsonCauchyExact.agda` directly specializes the EXISTING native `CompactLieLatticeGauge.holonomyGaugeCovariant` to a driven-forward / undriven-backward closed path. It derives `W_rel=U_driven U_base^{-1}`, identity if driven=base, gauge conjugation and class-function gauge invariance. It does **not** construct or typecheck a full 4D Dirac operator/charged CAR state. Exact Agda kernel receipt remains unavailable.

**P1 finite moving-background prototype DONE locally, 4D theorem OPEN:** `scripts/check_mmp_dirac_relative_cauchy_driven_20261025.py` committed, with expanded independently executed `/mnt/data/mmp_rce_maxcut/check_mmp_dirac_relative_cauchy_driven_20261025.py`. A 9-site two-spin Wilson–Dirac Hamiltonian with finite pulse and compensating time-dependent gauge scalar potential demonstrates `H'=GHG†+i Gdot G†`, `U'=G_T U G_0†`, exact local fermion lattice continuity, CAR projector/charge conservation, retarded Duhamel/Kubo derivative agreement and finite-gap passivity. U1 gauge and Kubo residuals fall ≈4x on step-halving (90/180/360), evidence for second-order integration. Local balanced three spatial source pulse yields **zero total circular Wilson phase, NONZERO local charge redistribution** (~0.02663) and positive input work (~0.007408); unbalanced phase 0.28 gives nonzero response. A pure gauge pulse is an independent NEGATIVE control. Finite "three regions" are electromagnetic profiles, **NOT separately dynamic plasma balls**. Do not infer physical ANEC, negative gravitational energy or traversability from the finite response.

**Physics critical path revised, in Pareto order:** (1) actual globally hyperbolic one-universe magnetic return background and physical charged spin-c Dirac CAR Hadamard covariance/state, not merely finite matrices or general-existence theorem; (2) continuum charged retarded Møller relative-Cauchy map for compact gauge/metric source change and charged gauge/spin line transport, with support/microlocal consistency; (3) relative **and absolute** locally covariant renormalized `<J>,<T>` including counterterms, gauge/diffeomorphism Ward, positivity/ANEC and state selection; (4) actual coupled Maxwell and Einstein equations with that SAME state and exterior return (no artificial source shutoff); (5) true three-region Maxwell–MHD finite-source dynamics and physical LLL dual-rail channel, with charge conservation, coherent information and causal front.

**Important negative control:** no net spatial Wilson-loop variation `δθ=0` does NOT imply zero local dynamical E or `δ<J>` in a finite fermion model; a change in closed holonomy alone does NOT quantify the physical source. Use electric field `E_j=−dot A_j−(V_j−V_(j+1))`, localized current and energy work as separate indicators.

New acceptance (local expanded equivalent PASS; GitHub exact-head runner/Agda kernel NOT claimed):
```sh
python3 scripts/check_mmp_dirac_relative_cauchy_driven_20261025.py
agda -i . DASHI/Physics/QFT/MMPDrivenRelativeWilsonCauchyExact.agda
```


**Second P4 pre-MHD source discriminator DONE as finite test, physical dynamics OPEN:** `scripts/check_mmp_three_independent_retarded_source_ports_20261025.py` separates three spatially localized **and separately timed** pulse sources (0.20–1.18; 1.04–2.12; 2.28–3.04) and constructs the retarded 9×3 local occupation susceptibility and measured 3×3 port matrix on one finite CAR ground state. Expanded local Python executed PASS: at observation t=1.7 the future third source has EXACT ZERO response, at t=3.2 it responds with norm .031738; earlier two respond at both times. Retarded Kubo versus direct finite amplitude differences <1.2e−6; total charge ≈4e−14 and positive injected work ≈.002745 for independently set amplitudes. This does NOT mean full relativistic microcausality or physically dynamic plasma materials: external A(t) is prescribed, no Maxwell field equation, no Hadamard renormalization, no Einstein saddle. Full source/method in [the dedicated report](MMPDrivenDiracRelativeCauchyPlasmaSourceMaxCut20261025.md). Preserve tests BOTH for (i) balanced **zero Wilson phase/nonzero local E response** and (ii) **future-supported causal zero response**.
