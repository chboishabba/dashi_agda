# 2026-10-25 max-cut: native Wilson/Maxwell prior art -> 2+1D magnetic three-port fermion backreaction

**PR:** [dashi_agda #1248](https://github.com/chboishabba/dashi_agda/pull/1248).  
**New committed checkers:** [magnetic plaquette + coupled CAR](../../scripts/check_mmp_three_port_2d_compact_u1_20261025.py), [independent tangent/dynamic gauge response](../../scripts/check_mmp_three_port_2d_tangent_20261025.py).

**Execution class:** local exact-source Python/NumPy/SciPy checks passed; not exact GitHub CI, Agda kernel, or Lean certification; original published continuum and numerical results remain attributable to their authors.

## Repository original-source donor audit

| Existing repo proof/adapter | Genuine reusable result | Promotion boundary |
| --- | --- | --- |
| `DASHI/Physics/YangMills/CompactLieLatticeGauge.agda` | Endpoint-indexed Wilson path, gauge covariance, loop class function/plaquette | Does not itself build dynamic Maxwell–Dirac matter |
| `DASHI/Promotion/MaxwellFiniteExteriorChainStrengthening.agda` | Finite symbolic exterior curvature and homogeneous Bianchi chain | Hodge *, sourced d*F=J, unit calibration deliberately blocked |
| `DASHI/Physics/YangMills/YangMillsLatticeStressWardSliceConservationExact.agda` | Finite periodic divergence telescoping and slice-charge conservation given local Ward law | Does not derive source-selected continuum stress tensor |
| `DASHI/Physics/YangMills/BalabanSU2PolarizationWardDerived.agda` | Ward response from same-action gauge invariance | SU(2) finite polarization does not equal our U(1) fermion Hadamard state |
| `DASHI/Physics/QFT/AQFTCarrierAlgebraQuotientSurface.agda` | Explicit typed AQFT time-slice/Cauchy obligations | Time-slice construction itself still open |
| `DASHI/Physics/QFT/MMPDrivenRelativeWilsonCauchyExact.agda` (PR #1248) | Algebraic background-relative Wilson contour/holonomy | No noncompact 4D spin-c propagator |
| `dashi_lean4` PR #85 | Conditional two LLL rail labels and erasure threshold; finite charge-sector distinctions | No selected physical rail wavefunctions or capacity |

These sources were *inspected and used as conceptual/formal-donor owners*. The numerical scripts do not import Agda; there is no claim that their matrix identities have an Agda kernel proof. **Do not duplicate** the generic Wilson or finite-divergence theorems as new theory.

## Original scientific roots and independent extensions

- F. Hebenstreit, J. Berges, D. Gelfand (2013), *Simulating fermion production in 1+1 dimensional QED*, **Phys. Rev. D 87**, 105006, DOI `10.1103/PhysRevD.87.105006`.
- V. Kasper, F. Hebenstreit, J. Berges (2014), *Fermion production from real-time lattice gauge theory in the classical-statistical regime*, **Phys. Rev. D 90**, 025016, DOI `10.1103/PhysRevD.90.025016` (includes 3D fermion/gauge backreaction).
- Y. Shi, J. Xiao, H. Qin, N. J. Fisch (2018), *Simulations of relativistic quantum plasmas using real-time lattice scalar QED*, **Phys. Rev. E 97**, 053206, DOI `10.1103/PhysRevE.97.053206`. This is an external structure-preserving exterior-calculus *scalar* QED precedent, not the source of a Dirac or 4D wormhole proof.
- Wilson, Kogut/Susskind and the original 2018/2023 Maldacena–Milekhin–Popov wormhole construction retain independent authorship/physics status. These references establish methods or models, not direct experimental evidence for a three-plasma gravitational device.

## Concrete finite construction

One periodic **3×3 spatial torus**: nine sites, two Dirac spinor components each, eighteen positively oriented links (x and y), nine plaquettes. With incidence `D: links→nodes` and plaquette coboundary `C: links→plaquettes`, the exact integer chain identities are

```text
D Cᵀ = 0;   C Dᵀ = 0
B_plaquette = C theta
theta -> theta + Dᵀ chi  =>  C theta unchanged
```

The rank-nine spectral CAR projector is the negative-energy eigenspace of one explicitly selected Hermitian finite Wilson–Dirac `h(0)`. It has a dimensionless spectral gap ≈0.89519. We **choose** a fixed neutralizing site background equal to its initial density; there is no dynamically derived plasma/ion material.

The three separate external link-current ports have spatial coordinates `(1,0,x)`, `(0,1,y)`, `(2,2,x)`; non-overlapping/partially overlapping windows `(0.2,1.18)`, `(1.04,2.12)`, `(2.28,3.04)`; amplitudes `(0.18,-0.14,0.11)`. All use prescribed compactly supported sin⁴ windows. External **charge** evolves by `rho_ext_dot = D I_ext`. This correctly accounts for otherwise non-divergence-free external currents.

One **single finite Hamiltonian/action** determines all matter and Maxwell terms:

```text
Etotal = Tr(P h(theta)) + (g2/2) sum(E_link²)
         + (1/g2) sum_plaquettes [1-cos((C theta)_p)]
i Pdot = [h(theta), P]                   (one CAR state)
theta_dot = g2 E
E_dot = -J(P,theta) - Cᵀ sin(C theta)/g2 + I_ext
J_e = ∂Tr(P h(theta))/∂theta_e
rho_ext_dot = D I_ext
```

With `g2=0.35`, the discrete matter-current continuity `dn/dt=-D J` plus `D Cᵀ=0` gives `d/dt[D E - (n-n_background) - rho_ext]=0`; and the Hamiltonian derivative gives `Etotal_dot=g2 E·I_ext`. Both are exact algebraic consequences of the selected finite differential equations; the local scripts independently check their numerical residuals.

The compact plaquette term creates **magnetic field energy and a curl force**. The previous 1D circle has no nontrivial local plaquettes. Total oriented flux over the trivial periodic torus is zero, **not** an MMP magnetic charge, and no selected 4D spin-c bundle has been built.

## Executed local evidence (2026-10-25)

The GitHub-committed source bytes match the locally executed files' exact length and codepoint sums, and local SHA-256 are recorded below. Both local scripts executed successfully:

```sh
python3 scripts/check_mmp_three_port_2d_compact_u1_20261025.py
python3 scripts/check_mmp_three_port_2d_tangent_20261025.py
```

| At t=3.4 on 3×3 finite torus | Local result |
| --- | ---: |
| Gauss max residual | 6.054e-16 |
| Local matter charge Ward max residual | 5.857e-17 |
| CAR projector idempotence norm | 2.909e-15 |
| Total energy–source-work residual | −1.377e-14 |
| Positive externally supplied work and energy gain | +0.0013762724 |
| Magnetic plaquette flux norm | 0.0152403 |
| Magnetic plaquette energy | 0.000331808 |
| Magnetic force norm | 0.0837446 |
| Matter density-change norm | 0.000936434 |
| No-magnetic-force electric-link difference | 0.0764516 |
| **No-fermion-current** Gauss violation | 0.000653273 |
| Weak-vs-strict solver density norm difference | 8.72e-12 |

The independent tangent checker constructs `delta J` by **differentiating the same fermionic Hamiltonian**, including both `Tr(delta P dH)` and `delta theta Tr(P0 d²H)`. It checks magnetically coupled tangent dynamics against centered full nonlinear evolution at source amplitudes 0.04 and 0.02, with nearly fourfold finite-difference error reduction where truncation dominates; exact early non-response of future third port; three-port linear superposition error ≈7.81e-12; linearized Gauss ≈1–2e-16. The **full nonlinear driven** static-site-gauge transform remains covariant with final fermion projector error ≈1.92e-15 and electric field error ≈3.13e-13. Omission of the magnetic force changes the linear electric response norm ≈0.07645.

Local source SHA-256:
- `check_mmp_three_port_2d_compact_u1_20261025.py`: `ebad983577fc77897e15c602439f298b734a075c5d1222fd2cdbc50dbf92eb9b`
- `check_mmp_three_port_2d_tangent_20261025.py`: `bc54c3ef7e21bb4fccabfeb3f6f16c660cb756a0bfb086ccf53618f1dc4d13d1`

**Adversarial distinctions:** Gauge covariance is dynamically tested, not just one conjugate Wilson loop. We have conserved matching external charge (no fictitious charged source leakage), magnetic force feedback (no merely prescribed B), and explicit matter-feedback ablation (a knowingly inconsistent negative control). None yields negative physical null energy or quantum channel capacity.

## Phase/roadmap decisions

- **P0:** New reproducible finite 2D exact-source script files and local receipts. GitHub workflow and Agda/Lean kernel receipts not claimed.
- **P1:** Free-Dirac Hadamard existence literature + native Cauchy/Wilson carriers are **donors only**. Select a 4D spin-c/gauge background and a state on the actual same-universe magnetic-return topology, and derive a globally admissible two-point function with local-covariant stress/current/renormalization.
- **P2:** The new 2D compact U(1) **genuinely couples** fermions and magnetic/electric fields, but the global self-consistent renormalized Einstein–Maxwell–Dirac state is still OPEN. A two-dimensional torus is not a wormhole or full Maxwell–MHD system.
- **P3Q:** Lean #85 finite LLL rail/erasure is logically independent and cannot inherit a physical channel from these finite bulk energy checks. Need actual rail wavefunctions, accessible endpoints, state scattering and environment/charge sector.
- **P4:** Three independently driven *electromagnetic current ports* with 2D magnetic backreaction are implemented, but externally controlled physical three **plasma material regions** and experimentally calibrated fields are not. Extend to 3+1D with conserved material stress/Maxwell sources before gravitational response.
- **P5/P6:** No external gravity measurement, exotic stress or traversability. Optional horned/C3/Monster content is not on the source-closure critical path without an actual same-object morphism.

**Largest remaining hard gate:** P1 selected 4D globally Hadamard-renormalized Dirac state, and then P2 one same-state Einstein–Maxwell fixed point. Finite gauge coupling is not a substitute.


## Additional 2025–2026 SOTA calibration: topological gauge-matter diagnostics

Original-root lineage (not DASHI inventions or proof inputs):
- **Bharadwaj, Rosanowski, Singh, di Tucci, Peng, Jansen, Funcke, Luo**, *Hamiltonian lattice QED3 with one and two flavors of Wilson fermions: Topological structure and response*, arXiv:2603.05616 (original preprint 5 March 2026), **Physical Review D accepted 10 September 2026**, DOI `10.1103/kc9m-xv9h`. Their gauge-invariant Chern/current-correlator diagnostics concern a quantum Hamiltonian QED3 with Gauss-law matter/gauge coupling. Our **classical** continuous link fields and finite spectral CAR covariance neither reproduce a many-body gauge Hilbert space nor establish an integer Chern invariant.
- **Rosanowski, Crippa, Funcke, Itaboraí, Jansen, Singh**, *2+1D QED at finite density on a quantum computer*, PRD **114** 014501 (1 July 2026), DOI `10.1103/3ntp-l3s7`, develops gauge-invariant state/constraint preparation in a small **quantum hardware** lattice, not a physical source for our semiclassical externally driven port.
- **Bender, Emonts, Zohar, Cirac**, *Real-time dynamics in 2+1d compact QED using complex periodic Gaussian states*, arXiv:2006.10038 (2020), a separate variational *compact gauge quantum-state* route; we do not conflate their Gaussian gauge ansatz with our finite fermion projector.

**Roadmap promotion gate:** treat nonzero local `C theta`/plaquette magnetic energy as a dynamical finite Maxwell observable, **not** a quantized magnetic bundle or Chern phase. To test topology, implement a parameter family of gapped **gauge-invariant** ground states, a bundle over twisted boundary phases, and curvature/Chern or physically measurable Hall-response consistency; independently benchmark lattice-size, discretization, fermion flavor, backreaction and charge sector. Even proving a lattice Chern number would not provide exotic negative stress, 4D magnetic-return topology or traversability. Do not displace P1 globally selected 4D Hadamard state.
