# Three-source finite U(1) gauge/Dirac backreaction max-cut (2026-10-25)

**Implementation:** `scripts/check_mmp_three_port_gauge_backreaction_20261025.py`; draft dashi_agda PR #1248.
**Evidence class:** locally executed, bounded 9-site semiclassical gauge lattice; **NOT** a 4D curved Hadamard/Eintein-Maxwell-Dirac proof, plasma experiment, or GitHub CI receipt.
**Locally executed file SHA-256:** `641c1276e5e2cc548d6d0148c87b0033b42f17521ea9b856a3cf185060a0b9ab`.
**Acceptance:** `python3 scripts/check_mmp_three_port_gauge_backreaction_20261025.py` (Python, NumPy and SciPy). No exact remote-run receipt asserted.

## Original-root / descendant ownership

- **Wilson:** 1974 lattice gauge parallel transport; the native DASHI `CompactLieLatticeGauge` holonomy source remains the proof owner of generic gauge-path transformations.
- **Hebenstreit, Berges & Gelfand:** *Simulating fermion production in 1+1 dimensional QED*, Physical Review D **87**, 105006 (2013), DOI `10.1103/PhysRevD.87.105006`: actual published real-time fermion/gauge backreaction work.
- **Kasper, Hebenstreit & Berges:** *Fermion production from real-time lattice gauge theory in the classical-statistical regime*, Physical Review D **90**, 025016 (2014), DOI `10.1103/PhysRevD.90.025016`: original classical-statistical fermion/gauge coupled methods, also in larger dimensional models.
- **DASHI prior model:** same 9-site, 2-component Hamiltonian and three separately timed source windows as `scripts/check_mmp_three_independent_retarded_source_ports_20261025.py`, plus the finite Dirac relative-Cauchy donor. The **new** implementation replaces prescribed electromagnetic link angles by self-consistently evolving electric links and fermion-current feedback.
- **Maldacena–Milekhin–Popov (2018/2023)** retain attribution for their separate actual wormhole construction; Sanders, Zahn, Gérard–Stoskopf and Capoferri–Murro retain authorship for their own distinct continuum Cauchy/Hadamard results. None is proved or substituted by this finite checker.

## Mathematical model, signs and conservation

At nine periodic spatial sites, two complex spinor components per site give an 18 × 18 Hermitian Wilson–Dirac single-particle matrix `h(theta)` with nearest-neighbour transport `exp(i theta_j) B`. The rank-nine negative-energy projector `P_0` of `h(0)` is the initial state. We select fixed neutralizing background charge `nbar_j = tr P_0[j,j]` **by hand** to make the unforced initial configuration Gauss-neutral; this is not a derived physical ion density.

With dimensionless `g2 = 0.35`, temporal gauge and external driven **classical** link currents `I_j`, the model solves:

```text
i dP/dt = [h(theta), P]
dtheta_j/dt = g2 * E_j
dE_j/dt = -J_j(P,theta) + I_j
drho_ext,j/dt = I_j - I_(j-1)
J_j = d Tr[P h(theta)] / dtheta_j
```

This fixes the orientation of fermion current by the **same** Hamiltonian that evolves `P`; it is not independently fitted. The site current continuity relation is `dn_j/dt = J_(j-1)-J_j`. The constraint

```text
G_j = E_j - E_(j-1) - (n_j - nbar_j) - rho_ext,j
dG_j/dt = [-J_j+I_j] - [-J_(j-1)+I_(j-1)]
           - [J_(j-1)-J_j] - [I_j-I_(j-1)] = 0
```

is a direct algebraic consequence of those equations. Explicit source charge is **necessary** because the three localized external link currents are not divergence-free on a 1D ring. The charge/current port is a prescribed external controller, **not** a dynamically simulated plasma ion/fluid.

The common energy and external work obey

```text
H_total = Tr(P h(theta)) + g2/2 * sum_j E_j^2
dH_total/dt = g2 * sum_j E_j I_j
```

because `Tr[(dP/dt)h]=0`, `partial_theta H_fermion = J`, and the `+J` and `-J` terms cancel. This identity is **finite model algebra**, not a curved 4D Ward stress-tensor result. The temporally driven fermion/gauge system is not isolated; supplied work is tracked.

## Source ports, tests and receipt

The three independent link ports are at sites (1,4,7), acting over respective time windows `(0.2,1.18)`, `(1.04,2.12)`, `(2.28,3.04)`. Each has a supported `sin^4` current pulse with amplitudes `(0.18,-0.14,0.11)`. Numerical complex-valued `DOP853` integration to time 3.4 uses `rtol=1e-10`, `atol=1e-11` and a maximum step 0.045.

**Locally executed results** (not GitHub CI):

| Quantity at t=3.4 | Value |
| --- | ---: |
| maximum absolute Gauss residual | 4.90e-16 |
| fermion total-charge residual | 1.19e-15 |
| CAR projector idempotency norm | 2.72e-15 |
| local continuity residual | 4.03e-17 |
| abs(energy - initial energy - integrated source work) | 2.36e-15 |
| total energy gain, equal to source work | +0.0014983047 |
| local fermion density-change norm | 0.0040895147 |
| coupled electric-link norm | 0.08981156 |
| coupled minus source-only electric-link norm | 0.0033217743 |
| undriven local density-change norm | 5.09e-16 |
| early t=1.7 third-port-only state difference | 2.83e-15 |
| static U(1) covariance residual | 4.59e-16 |
| loose-versus-strict solver density difference | 3.05e-12 |

The source-only electric benchmark is the analytical integral `I_j dt = amplitude × (3/8) × pulse_width` for the supported `sin^4` pulses. It would NOT preserve the full matter-plus-external Gauss constraint if fermions respond; the nonzero difference is evidence of actual feedback **within this model**. Numerical precision does not make a physical prediction beyond the model.

Negative control: the third source is inactive before `t=2.28`, and a third-port-only run at `t=1.7` is equal to the undriven ground state within numerical tolerance. This demonstrates time-support causality of the **controlled finite evolution**, not continuum relativistic microcausality or an FTL constraint.

## Next physically necessary max-cut gates

1. **P1 continuum carrier**: choose one smooth globally hyperbolic same-universe return-path metric and fixed spin-c/gauge bundle; build the curved 4D Dirac Cauchy evolution plus an actually selected CAR Hadamard covariance, rather than only general free-state existence or finite matrix smoothness.
2. **P1 covariant sources**: on that same background/state compute all renormalized local charged current and tensor components with local Hadamard subtraction, anomaly, finite counterterms, diffeo and U(1) Ward identities, for both static and driven perturbations.
3. **P2 coupled 3+1D fields**: replace 1D electrostatic link dynamics by spatial Maxwell constraints, transverse radiative modes, specified actual material/ion sources with stress-energy and boundary work, and then feed SAME state current/tensor into Einstein+Maxwell. Demonstrate constraint convergence, stability and an actual geometry/state fixed point.
4. **P3/Q and P4 discrimination**: compare identical final background, charge sector and environmental leakage for two LLL equal-charge rails; measure spatially resolved state-dependent negative energy/null flux, causal arrivals and response to three independent 3D drive profiles, including non-C3 controls. Do not promote a finite lattice energy gain into negative ANEC or traversability.
5. **P0 evidence governance**: rerun full **committed** checker at the exact PR SHA in a known Python environment; build formal Agda/Lean source interfaces only with explicit external hypotheses and exact-kernel receipts. The executable was locally run, not by a GitHub runner.

**Bottom line:** this max-cut closes a narrow but important earlier omission: gauge-field evolution now includes fermion-current feedback and conserved source charges. It does NOT close the 4D renormalized Dirac state, self-consistent wormhole or plasma-gravity gates.

## Additional closed-loop linear response acceptance (2026-10-25)

**Committed:** [same-coupled-background tangent/Kubo-like three-port checker](../../scripts/check_mmp_three_port_backreaction_tangent_20261025.py), locally executed file SHA-256 `cc5fa584c29e7e40900810f32a50b623eb3fb03f122be3c3db880d930ddc0cc9`.

For the SAME 18×18 reference Hamiltonian `H0` and ground-state projector `P0`, its tangent equations contain BOTH `[H0,delta P]` and `[delta h,P0]`, with `delta h = sum_j delta theta_j partial_theta_j h`. The induced material link current is computed by differentiation of the SAME fermionic Hamiltonian:

```text
delta J_j = Tr(delta P * partial_theta_j h) +
            delta theta_j * Tr(P0 * partial_theta_j^2 h)
delta E_j_dot = -delta J_j + I_j
```

This closes a first-order *dynamical* retarded source-response loop, rather than reusing a prescribed-field Kubo result. The computed responses satisfy linearized Gauss law and superpose across the three source ports; a third pulse beginning after time 2.28 has zero response at time 1.7.

**Actual local validation:** at final time 3.4 the first/second/third source density-response norms are 0.00606879 / 0.02696654 / 0.00653500 per unit input. At finite amplitude `epsilon=0.02`, central finite-difference errors are 1.81e-7 / 2.10e-8 / 8.81e-10; halving `epsilon` to 0.01 reduces the first and second errors almost fourfold, compatible with quadratic truncation. Three-port linear superposition residual is 1.24e-14. The **source-only** tangent comparison (deliberately deleting `-delta J`) violates the full Gauss constraint by norm 0.004202 and differs in electric field by norm 0.003321. This is a carefully labelled negative control, **not** an alternate physical solution.

This linear checker remains finite matrix / 1+1D electrostatic only. A tangent linear response on fixed flat ring with hand-prescribed sources does not imply a true curved 4D Hadamard retarded response, exact light-cone locality, physical MHD, quantized gauge field, or spacetime gravity. It does not use an Einstein stress tensor.

**Second acceptance:** `python3 scripts/check_mmp_three_port_backreaction_tangent_20261025.py`.
