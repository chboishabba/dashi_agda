# Flux-normalized curved Dirac scattering → quantum channel: Oct 24 max-cut

**Owners and non-promotion:** PR #1248, building on existing effective shooting source `check_mmp_global_effective_bvp_replay_20261024.py` and previously committed finite Wilson–Dirac/Bell protocol `check_mmp_teleportation_channel_bridge_20261024.py`. The quantum teleportation, quantum-energy teleportation (QET), causal-front and experimental-claim separation already belongs to PR #1163 (`CausalTransportFTLObligationsExact`, `CausalTransport2026SourceAtlasExact`); TPS/subsystem selection owner #1128. We do not invent a new generic quantum ontology or assume these sibling branches are merged.

## Original source and attribution

- Maldacena, Milekhin, Popov, `arXiv:1807.04726` (2018), *Classical and Quantum Gravity* 40 (2023) 155016, DOI `10.1088/1361-6382/acde30`: original 4D magnetic charged-fermion wormhole, where closed field-line return paths define fermionic state. This PR's metric is still the **piecewise two-ended reduced Polyakov+finite spherical tower stress with an imposed RN source cutoff**, NOT their same-universe closed-line state or original physical solution.
- Sabín, *Mapping curved spacetimes into Dirac spinors*, *Scientific Reports* 7 (2017) 40346, DOI `10.1038/srep40346`: reference for 1+1D massless Dirac conformal reduction, not a proof of global 4D spinor scattering.
- Standard 1D stationary Dirac current-flux scattering, matched in *Scattering, bound states, and resonances in the one-dimensional Dirac equation via supersymmetric quantum mechanics* (EPJC 2026, DOI `10.1140/epjc/s10052-026-16228-4`). Flux ratios rather than bare spinor amplitude define R/T. This standard source does not establish physical MMP geometry.
- Bennett et al., *PRL* 70 (1993) 1895, DOI `10.1103/PhysRevLett.70.1895`: standard Bell-assisted quantum-state teleportation, distinct from physical Dirac propagation.
- Gao–Jafferis–Wall, *JHEP* (2017) 151 and Maldacena–Stanford–Yang (2017): holographic wormhole/teleportation connections; not a 4D Einstein–Maxwell–Dirac source identity.
- Existing DASHI source authors, code and finite probes retain attribution; local Python numerics are neither kernel-verified Agda/Lean theorems nor experiments.

## Implemented exact model

On a static reduced radial metric `ds²=-N(x)² dt²+dx²+r(x)²dΩ²`, define optical coordinate `z=∫dx/N(x)`, and separate spherical spin-c angular eigenmodes with magnetic flux index `q∈Z`, radial 2D massive eigenvalue `m_n(r)=sqrt(n(n+|q|))/r`.

The rescaled fixed-background radial Dirac equation takes the **source-assumed reduced** form
`H_n=-i σ_x ∂_z+V_n(z)σ_z`, `V_n(z)=N(z)m_n(r(z))`.
One must fix the rescaling and inner product from actual 4D spinor decomposition before claiming a physically exact same-object 4D wave equation. The n=0 LLL has `V_0=0`: in this **massless 1+1D conformal limit** it is exactly reflectionless on a static metric. Massive towers n=1,2 encounter a nontrivial throat/mouth-dependent effective barrier.

A transfer matrix M is integrated for `ψ'= (i E σ_x -V_n σ_y +i A_z I)ψ`. Since `A†σ_x+σ_x A=0` for real E,V,A_z, `M†σ_x M=σ_x`, conserving incoming minus outgoing Dirac flux. Midpoint constant-cell matrix exponentials give an individually J-unitary step; source-run numerical propagation is second-order in optical-cell width. In the σ_x eigenbasis, with a left-incident unit-flux mode and no incoming right mover, `r=-B21/B22`, `t=det(B)/B22`, where `B=U†MU`. **The determinant is essential under a nonzero Abelian gauge phase; blindly using `1/B22` would produce the wrong transmission phase.** `R=|r|²`, `T=|t|²` and `R+T=1`.

A bounded gauge field along an **OPEN** path changes the transmission phase by `e^{i∫A_z dz}` but does not improve T. A **CLOSED** Wilson phase can change the quantum state and Casimir energy; the two are NOT the same effect. A pure U1 gauge transformation does not magically engineer a transparent massive barrier.

## Geometry/time normalization finding

The prior optical-length self-consistency fixpoint at `q=12,L_throat=22.516301125725` used a `N(throat)=1` time coordinate. Reconstruct the RN junction `R=12.79381947, M=5.99725136, Q=6` and **rescale the lapse** to the asymptotically normalized RN clock by `λ=sqrt(f_RN(R))/N_inside(R)=0.0139837728724`.

Consequently the **physical asymptotic-Killing-time** interior optical transit is `τ_infinity=20.5163011257/λ=1467.15062615`, while the local throat-coordinate result was `20.5163011257`. The imposed optical global circumference L=22.5163 in throat time converts to `1610.173544` in infinity time. The arbitrary hypothetical exterior return time 2.0 in throat units corresponds to `143.022918` infinity units, **NOT** two external-clock units.

These numbers are geometrized/dimensionless; they are NOT milliseconds, photon times, or a measured communication shortcut. With two distinct RN infinities instead of one connected outside route, the original MMP return loop remains unpaid.

## Numeric results and controls

**Local executed source-equivalent scripts (GitHub exact-head runner not claimed; results below use local-mass flux eigenmodes at the finite RN endpoints):**
- `scripts/check_mmp_dirac_flux_scattering_20261024.py`: effective metric read from shared shooting owner with optional `with_profile=True`; analytically validated finite constant-mass Dirac square barrier above/below threshold; exact V=0 massless reflectionlessness; J-unitary transfer / R+T=1; open U1 phase covariance; cutoff values R_out=60,120,240.
- `scripts/check_mmp_dirac_scattering_precision_20261024.py`: cutoff R_out=120,240,480 vs step width 0.30,0.15,0.075 at E=0.55,n=2. **The transfer discretization converges** (T≈0.9987228783,0.9987229111,0.9987229198); separate RN exterior truncation does NOT converge to infinity for all low energies.

At selected `R_out=240` and conserved-energy E measured with asymptotic RN clock (model units):

| E | LLL n=0 T | massive n=1 T | massive n=2 T | selected n1/n2 mean successful η | ideal postselected entanglement fidelity |
|---|---:|---:|---:|---:|---:|
| 0.20 | 1 | 0.99986528 | 0.000034463 | 0.49994987 | 0.50587071 |
| 0.55 | 1 | 0.999999994 | 0.999999997 | 0.999999995 | ~1.00000000 |
| 1.00 | 1 | 0.9999999996 | 0.99999999999 | 0.9999999998 | ~1.00000000 |

The **selected two-mode channel** assumes coherent preparation of two *different angular modes*, K=diag(t1,t2), and an explicit erasure flag. Its successful transmission is input-dependent if |t1|≠|t2|, so it is not an input-independent ideal erasure channel. Completing with Kraus operators from sqrt(I−K†K) makes the channel CPTP. In particular η≈0.49995 at E=.2 is **NOT** a high-fidelity arbitrary qubit link: the two modes have nearly maximal selective attenuation and the conditional normalized entanglement fidelity is only ≈0.50587.

**Source of uncertainty and scope:** With flux-normalized local-mass outgoing/incoming lead spinors, E=.20 n1 T=0.99982692 (R=120), 0.99986528 (R=240), 0.99985399 (R=480); n2 T≈(3.4642,3.4463,3.4478)×10^-5. Earlier preliminary values (n1 .986447/.997363/.999743 and n2 2.45/2.78/3.39×10^-5) used **inappropriately massless spinors at the finite-radius cutoff**, so must be regarded as a boundary-mismatch diagnostic, NOT the primary physical approximation. Do NOT extrapolate any displayed value to infinity without a Coulomb-tail/long-range scattering boundary prescription and quantified numerical limit. Optical profile interpolation, finite KK truncation, q/L, state, assumed renormalization, and original geometry sourcing introduce independent, larger model uncertainty.

**Signal-front causality:** the continuum Dirac PDE is first-order symmetric-hyperbolic, principal speeds ±1 in optical z. A local mass perturbation does not alter its principal characteristics; therefore a retarded disturbance in the reduced system cannot propagate outside its optical light cone. An energy-resolved scattering coefficient or group/Wigner delay is NOT a speed-of-light or FTL measurement. The result does not establish no chronological pathologies in an unconstructed same-universe geometry.

## Pareto next phases

1. **P0 exact-head reproducibility:** execute the now-committed new physics scripts and produce pinned GitHub CI output; the locally equivalent scripts and retrieved shared BVP owner were executed, not the merged exact PR head. Maintain output and conventions.
2. **P1 true global spin-c Dirac state and magnetic same-universe loop:** no physical MMP quantum source can be claimed merely from the source-truncated two-infinity effective metric. Solve global Hadamard renormalization, source/current and return path first.
3. **P2 physical Einstein–Maxwell–Dirac fixed point:** coupled `G=8πG(T_EM+<T>_ren)`, `∇F=<J>`, Dirac state, exterior geometry and no artificial stress cutoff.
4. **P3Q actual 4D scattering/channel:** extract asymptotically current-normalized 4D in/out modes from P1/P2 actual geometry, spin connection, complete S-matrix or retarded Green function, wavepacket support, encoded physical TPS, gauge holonomy, transmission/erasure/fidelity/front times, backreaction of injected pulse. Include right/left leads in SAME surrounding universe.
5. **P4 three-plasma control:** physical Maxwell–MHD current/boundary flows perturb the same fermion propagator AND metric. Contrast balanced C3 E·B null against envelope and holonomy perturbations with sign-adversarial quantum NEC + measured EM nuisance controls. Horned PR #1244 remains optional **nonabelian** connection without supplying the MMP U1 flux cycle.

## Executable acceptance

```sh
python3 scripts/check_mmp_global_effective_bvp_replay_20261024.py
python3 scripts/check_mmp_dirac_flux_scattering_20261024.py
python3 scripts/check_mmp_dirac_scattering_precision_20261024.py
python3 scripts/check_mmp_teleportation_channel_bridge_20261024.py
```

Locally equivalent tests PASS. Until exact GitHub runner output appears, they are **source-written acceptance commands**, not GitHub CI certification.


### Boundary-condition correction and residual Jost obligation (documented supersession)

The preliminary finite-radius scattering calculation used *massless* `σx` eigenvectors at the numerical boundary, although the spherically reduced massive term there remains `V_n=N(R) sqrt(n(n+|q|))/R ≠0`. That mismatch generates an artificial reflection contribution, particularly at lower E and smaller R. The corrected finite-radius boundary is the locally propagating massive Dirac eigenbasis with `k=sqrt(E²−V_n(R)²)`, flux-normalized spinors `(sqrt((E+V)/(2k)),±sqrt((E−V)/(2k)))` satisfying `u±†σx u±=±1`. Choose n>0 only when E>|V_n(R)|; n=0 keeps exact massless basis. The corrected matrix `B=U_out^{-1} M U_in` retains flux conservation. Exact constant-mass barrier and free massless tests deliberately use the correct massless *exterior* lead, as they must.

This correction is **not** the exact RN infinity solution, since `V_n(r)` still changes beyond the finite matching boundary. Replacing its tail by a constant-mass lead is an adiabatic finite-radius approximation. At E=.55,n2,R=240, midpoint step .30/.15/.075 yields corrected T=0.9999999968138/0.9999999967746/0.9999999967638; residual changes mostly at high precision. The range of cutoff values at E=.20 is now small but NONZERO, so the infinite-radius analytic Jost problem and full physical return-path S-matrix remain open. Finite-radius success near unity is not a validated independent physical-capacity measurement.
