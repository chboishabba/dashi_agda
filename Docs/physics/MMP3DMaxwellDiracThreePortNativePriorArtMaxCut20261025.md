# 2026-10-25: three-spatial-dimensional Maxwell/Dirac three-port max-cut

**Implementation:** dashi_agda draft [PR #1248](https://github.com/chboishabba/dashi_agda/pull/1248), files:
- [check_mmp_3d_maxwell_dirac_three_ports_20261025.py](../../scripts/check_mmp_3d_maxwell_dirac_three_ports_20261025.py)
- [check_mmp_3d_maxwell_dirac_tangent_20261025.py](../../scripts/check_mmp_3d_maxwell_dirac_tangent_20261025.py)

**Evidence class:** locally executed exact Python source (NumPy); GitHub head file lengths and checksums matched local exact code. **No Agda/Lean kernel or GitHub workflow receipt**. Flat periodic 3D space plus time, a *classical* dynamic compact U(1) spatial gauge field and a finite, free four-spinor occupied-orbital CAR covariance; **not** a 4D microlocal/Hadamard free Dirac quantum field on a wormhole and not an Einstein solution.

## Prior-art owners and roots (not reassigned)

- **Native DASHI**: `DASHI/Physics/YangMills/CompactLieLatticeGauge.agda` already proves generic endpoint-indexed Wilson holonomy and class-loop invariance; `DASHI/Promotion/MaxwellFiniteExteriorChainStrengthening.agda` represents homogeneous curvature/Bianchi and keeps source, Hodge and continuum Maxwell promotion blocked; `DASHI/Physics/YangMills/YangMillsLatticeStressWardSliceConservationExact.agda` proves finite periodic Ward telescoping; `DASHI/Physics/YangMills/BalabanSU2PolarizationWardDerived.agda` differentiates gauge-invariant actions, and `DASHI/Physics/Closure/G2DiscreteCurvatureCarrier.agda` marks the unfilled prime-lattice 2-cell-to-curvature consumer. This Python code does **not** directly instantiate that formal prime-lattice carrier or Agda proofs.
- **Previous sibling implementation**: Agda #1248 1D current-coupled U1 and 2D magnetic compact U1 checkers are finite donor provenance; their synthetic periodic 2D and 3D grids are not an MMP throat, an S² spin-c monopole, or a proof of Maxwell–Einstein closure.
- **Scientific origins**: Kenneth Wilson (1974) Wilson parallel transport/lattice gauge, Kogut–Susskind Hamiltonian lattice methods; K. S. Yee (1966) structured finite-difference Maxwell (DOI `10.1109/TAP.1966.1138693`), not a claim our compact action is the same as Yee's algorithm; F. Hebenstreit, J. Berges and D. Gelfand (2013) 1+1D quantum fermion/gauge real-time method (DOI `10.1103/PhysRevD.87.105006`); V. Kasper, F. Hebenstreit, J. Berges (2014) explicitly demonstrates lattice fermion production/backreaction in **three spatial dimensions** (DOI `10.1103/PhysRevD.90.025016`). The literature, not this PR, owns the original physical and numerical results.
- **Separate physical hypothesis**: Maldacena–Milekhin–Popov 2018/2023 magnetically charged closed-return-field-line wormhole; Gérard–Stoskopf free-Dirac Hadamard existence and Zahn charged-Dirac locally covariant renormalization, neither instantiated here. Lean #85 conditional spherical magnetic LLL rails do **not** follow from the zero-net-flux trivial 3-torus of this model.

## Exactly constructed finite same-object model

Cubic 3×3×3 periodic spatial graph `T³`: 27 vertices, 81 oriented links and 81 elementary oriented plaquettes, four-component 3+1D Clifford Dirac spinors (108 one-particle components) and a rank-54 negative-energy projector represented by occupied 108×54 orbitals `V`. Four gamma matrices are explicit using tensor products of Pauli matrices, with anticommutation checked. A spatially nonuniform mass plus Wilson term lifts doublers in the finite reference spectrum; source-selected initial single-particle gap ≈1.7538375 (dimensionless). **That finite gap is not a continuum Dirac mass gap.**

From integer incidence operators `D: C¹→C⁰` and `C: C¹→C²`:

```text
D Cᵀ = 0     C Dᵀ = 0
rank(D)=26, rank(C)=52
81 = 26 longitudinal + 52 coexact/transverse + 3 harmonic links
```

The positive link Hodge Laplacian `DᵀD+CᵀC` has exact numerical spectrum 0 (3 times), 3 (18), 6 (36), 9 (24), matching Fourier modes on the selected **finite** T³. Hence the discrete divergence of the magnetic curl vanishes and a pure gauge site potential cannot change plaquette flux. Three harmonic one-forms reflect the selected T³ topology; **they are not the MMP S² flux index or a 4D fermionic boundary holonomy.**

A single specified finite Hamiltonian produces all coupled dynamics:

```text
H_total = Tr(P h(theta)) + (g²/2) sum E_link²
          + (1/g²) sum_faces [1-cos((C theta)_face)]
P = V V†,  i V_dot = h(theta) V
theta_dot = g² E
E_dot = - J(P,theta) - Cᵀ sin(C theta)/g² + I_ext
rho_ext_dot = D I_ext
J_l = ∂ Tr(P h(theta)) / ∂ theta_l
```

We use dimensionless `g²=0.35`, Wilson coefficient `r=0.42`, three driven link current sources at `(1,0,0,x)`, `(0,1,1,y)`, `(2,2,2,z)`, with independently supported `sin⁴` pulses over windows `(0.2,1.18)`, `(1.04,2.12)`, `(2.28,3.04)` and amplitudes `(.18,-.14,.11)`. The external local charge `rho_ext` is **not optional**: it is needed for exact continuity when external link currents have a nonzero site divergence. The static neutralizing background `nbar = n(P_initial)` is **chosen by hand**, not a solved ion distribution.

Finite exact Ward/Gauss/energy identities from the SAME action and orientation:

```text
n_dot = -D J
G = D E - [n(P)-nbar] - rho_ext
G_dot = 0  (using D Cᵀ=0)
H_total_dot = g² E · I_ext
```

The model has genuine electric-link and compact magnetic-plaquette dynamics. It lacks spatial material constitutive equations, a quantized photon field, Minkowski-limit renormalization, physical calibrated units and metric backreaction. A gauge-field Euler step is not an electromagnetic plasma-ball experiment.

## Local executed evidence and numerical controls

Local Python/NumPy execution, no CI head run; earlier coarse `dt=.03` failed Gauss/orthogonality/energy acceptance and was **not** promoted. RK4 step refinement: `dt=.004` gives:

| Metric at final t=3.4 | Local result |
| --- | ---: |
| Gauss maximum site residual | 4.5983e-11 |
| Local matter-current Ward maximum | 2.7037e-16 |
| Four-spinor occupied-orbital orthonormality residual | 1.9783e-10 |
| Total fermion charge deviation | 1.0374e-9 |
| Total energy minus starting energy minus integrated source work | 3.0699e-9 |
| Externally supplied work | +0.0014166354 |
| Magnetic compact plaquette energy | +0.0005083521 |
| Matter density change norm | 0.0008832140 |
| Magnetic field-force norm | 0.13682052 |
| Magnetic-force ablation: electric-link difference | 0.08216119 |
| Fermion-backreaction ablation: **broken** Gauss maximum | 0.0003888635 |
| Coarse `dt=.008` versus refined `dt=.004` density difference | 6.2148e-9 |
| Premature third-port-only physical projector difference at t=1.7 | 3.1281e-9 |
| Driven site-gauge covariance, full projector | 1.2025e-14 |

**Negative-control nuance:** a freely evolving occupied-orbital matrix is not equal to itself at later time because its columns acquire unobservable phases. The third-port pre-activation control compares the **physical projector** `V V†` rather than comparing the orbitals to time-zero columns. Failure of the coarse RK4 is a numerical convergence warning, not evidence of a physical constraint anomaly. Error tolerances are for this finite model and must be re-evaluated under larger volumes, different couplings and longer evolution.

The independent [tangent checker](../../scripts/check_mmp_3d_maxwell_dirac_tangent_20261025.py) derives the occupied–unoccupied block `z` of `delta P` in the eigenbasis of the **same H0**, avoiding spurious occupied-orbital gauge rotations. Its source derivative includes the instantaneous fermion-current curvature and the **same magnetic** `Cᵀ C theta/g²` force; the external charge and Gauss constraint are differentiated too.

At `t=3.4`, for ports 1/2/3:
- retarded density-response norms per unit drive: `0.0027967363`, `0.0037699613`, `0.0041972049`;
- centered finite-difference error at source amplitude `0.30`: `7.249e-8`, `1.374e-7`, `1.021e-7`;
- at `0.15`: `2.095e-8`, `3.027e-8`, `2.340e-8`. Ratios approximate 3.46, 4.54, 4.36, consistent with quadratic finite difference plus integration truncation;
- linear Gauss norms all < `2.2e-16`, three-port linearity norm `6.26e-18`;
- deleting induced matter feedback gives a `0.000886647` linear Gauss residual and deleting magnetic force shifts the electric response by `0.08216149`.

The earlier overly broad tangent acceptance loop (checking both early and late nonlinear finite differences sequentially) took too long; the final committed checker tests all three independent ports at the final observation time, while the nonlinear source-only pre-activation projector negative control at `t=1.7` separately checks temporal support. The committed two-script acceptance passed in this local environment, with execution receipts below.

## Phase/deliverables and non-promotions

- **P0 bounded finite reproducibility:** meaningful 3-spatial-dimensional, four-spinor, same-energy/action and gauge-consistent positive numerical results. Freeze exact script source, parameter values, SHA-256, full JSON output, and periodically compare GitHub head to local execution. Source files are Python—not imported into formal Agda or Lean—and require future exact-head CI validation.
- **P1 decisive global source:** still OPEN. An actual four-dimensional *curved and noncompact* Dirac operator on the selected spin-c same-universe magnetic-return geometry, one globally selected Hadamard CAR covariance, and consistent local-covariant renormalization of `<J>,<T>`, including angular/radion components, current continuity, finite local counterterms, and state-dependent Wilson/Schwinger response.
- **P2 fixed point:** still OPEN. No self-consistent four-dimensional Einstein–Maxwell–Dirac spacetime or negative ANEC deduced from this flat 3-torus Hamiltonian.
- **P3Q channels:** still OPEN physically; Lean #85 conditional dual-rail and erasure conditions cannot reuse a flat trivial magnetic bundle as proof of spherical S² LLL index or physical channel capacity.
- **P4 real plasma:** three separately timed classical electromagnetic sources and field backreaction are modeled, but no independently solved three **3D material plasma** regions, current/charge closure via real ions/electrons, thermal/mechanical stresses, radiation losses or lab calibration.
- **P5 physical claim:** no gravity measurement, geometric traversability, reproducible antigravity/teleportation apparatus or wormhole preparation.
- **P6 optional donors:** 369/729, exceptional algebra, horned sphere, Golay and C3 remain downstream until an explicit same-operator source or measurable discriminator is constructed.

**Pareto after this max-cut:** stop multiplying toy dimensions solely for aesthetics. Quantify continuum/volume/regulator scaling and pursue the actual selected 4D Hadamard state, fixed counterterm, **same** renormalized Maxwell current/tensor and gravity fixed point; keep discrete Gauss/energy/Hodge as a controlled finite regression.
