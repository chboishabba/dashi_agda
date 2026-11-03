# Quantum teleportation × charged Dirac wormhole: source-first channel weld (2026-10-24)

**Canonical target:** PR #1248 physical MMP magnetic fermion wormhole. **Sourced teleportation owner:** Agda PR #1163, `DASHI/Physics/Foundations/CausalTransportFTLObligationsExact.agda` and `CausalTransport2026SourceAtlasExact.agda`, on branch `design/field-geometry-matter-maxcut-20261015`, not assumed merged. **Subsystem selection:** quantum-mereology PRs #1070/#1128 finite TPS, same-global-state pair-marginal / coordinate-chart gates, not automatic physically canonical input/output qubits. **Experimental scale donor:** Lou et al., *Hundred-Channel Reconfigurable Quantum Teleportation*, PRL **137**, 080801, published August 20 2026, DOI **10.1103/rfz9-3prw** (100 spatial optical modes with all-optical feedforward), not a materialized gravitational wormhole.

## Bottom-line contribution and attribution

Existing DASHI correctly separated state/gate teleportation, quantum energy teleportation (QET), carrier/particle transport, physical wormholes, and FTL. Until this round it did NOT derive a teleportation/comms channel from the finite curved fermion Hamiltonian used by PR #1248. This new tranche attaches a **selected finite quantum-information channel** to that operator, tests CPTP/gauge covariance and standard teleportation no-signalling, and explicitly records what is required before physical promotion.

Original teleportation protocol: Bennett et al., *Teleporting an Unknown Quantum State via Dual Classical and Einstein-Podolsky-Rosen Channels*, *Physical Review Letters* 70 (1993) 1895, DOI 10.1103/PhysRevLett.70.1895. Traversable wormhole / teleportation correspondence: Gao–Jafferis–Wall (2016 preprint; JHEP 12 (2017) 151, DOI 10.1007/JHEP12(2017)151); Maldacena–Stanford–Yang (2017) arXiv:1704.05333. **These are primarily AdS/BTZ/near-AdS2 dual constructions, not the same physical source as MMP 4D Einstein–Maxwell massless charged fermions** (Maldacena–Milekhin–Popov arXiv:1807.04726; CQG 40 (2023) 155016). ER=EPR is a conceptual relation, not a licence to identify models or claim signal FTL.

## Exact quantifiable finite Hamiltonian bridge

Use the existing PR #1248 finite Wilson–Dirac Hamiltonian structure on a 12-site circular lattice with a nonconstant lapse N_j, radius r_j, magnetic spherical KK mass n=1 at q=12, and a genuine U1 link gauge phase A_j. The selected physical encoding is a two-spinor input basis at site 1 and an output basis at site 5 (an explicit **chosen** TPS/subspace), with model time t. Define

```
U(t) = exp(-i H t),
K(t) = P_out U(t) P_in as a 2×2 spin block,
Q = I_2 − K† K >= 0.
E(ρ) = K ρ K† (output qubit) ⊕ Tr(Qρ) |erasure><erasure|.
```

The last expression is a **CPTP erasure channel** from input C² to output C² plus orthogonal loss flag, with Kraus operators built from sqrt(Q). Its Choi matrix is positive and its trace is preserved. The original H is Hermitian, so K is contractive. Gauge transformation H' = GHG† maps K' = exp(i(χ_out−χ_in)) K; success probability and singular values are gauge invariant. This is an actually operator-attached bridge, not an analogy about geometry.

Executed equivalent local Python script `/mnt/data/check_dirac_wormhole_teleportation_channel_20261024.py` PASS; new reduced repo script `scripts/check_mmp_teleportation_channel_bridge_20261024.py` is source-written and committed, **not claimed independently run at exact PR head**. Finite example source=site1, target=site5, q12, 12 sites, t=0.91: gauge covariance ~9.84e-16, Kraus trace residual ~1.35e-15 and minimum Choi eigenvalue ~-2.4e-22 (floating roundoff). Predeclared time-grid t∈[0,30] step 0.02 peaks at t=12.52: **mean success η=0.210412**, state-weighted entanglement fidelity 0.205399, **conditional entanglement fidelity 0.976177 after success heralding and the ideal calibrated polar-unitary correction**. Note the distinction: high conditional fidelity on accepted outcomes is NOT high unconditional success, nor a transmission-time/causal-front validation. These chosen dimensionless Hamiltonian parameters are illustrative; do not infer any MMP fidelity from them.

## Independent original Bennett-type LOCC benchmark

Using the shared |Φ+> Bell resource, measurement on input+Alice qubit yields four Bell outcomes each probability 1/4, and Bob's marginal **before the 2-bit classical correction** equals I/2 for every tested input (no-signalling). After classical messages and outcome-dependent Pauli corrections, tested state-transfer error <5e-16. This is a completely distinct LOCC resource from physically transmitting a spinor through the finite Dirac lattice. A finite lattice `exp(-iHt)` can have tiny nonzero amplitudes at arbitrarily short t; no relativistic front-speed, field microcausality or FTL theorem is established by the lattice fixture.

**Protocol identity boundaries:**
- **Teleportation:** Alice's Bell measurement + previously shared entanglement + two classical bits + Bob correction; an unknown state is reconstructed, not a particle sent via empty space.
- **Direct wormhole propagation:** a quantum excitation moves along a physical path; must derive flux-normalized retarded/advanced/LSZ scattering operators, and project onto *physically encoded* in/out subsystems.
- **Holographic traversable wormhole teleportation:** a theory-specific two-boundary coupling, gravitating backreaction, and dual many-body correlators/channel; Gao–Jafferis–Wall and Maldacena–Stanford–Yang cannot be silently imported into MMP.
- **QET:** conditioned extraction of local energy using correlations and classical communication, not freely transmitted negative stress/matter.
- **Lou et al. 2026:** 100 spatially factorized optical teleportation channels and measured fidelity thresholds; not a 100-channel gravitational/Dirac wormhole demonstration.

## Same-object next acceptance gates (ranked)

1. **P1/2 source & state:** construct same-universe magnetic closed return path, globally admissible spin-c charged Dirac state and covariantly renormalized four-dimensional action/stress/current. This remains the gravity **critical path**; teleportation is not a shortcut.
2. **Physically normalized one-particle scattering:** define external asymptotic in/out fermion solutions and flux-normalized `S_{mathrm{Dirac}}` or retarded Green function on the *same* coupled 4D geometry, with U1 parallel transport and spin connection; derive a valid K for physically realizable encoding and its environment/loss rather than assume chosen site subspaces.
3. **Quantum channel:** identify TPS/input/output, construct Choi CPTP/CP-TNI and erasure completion, compute transmission probability, entanglement and average state fidelity, phase/holonomy dependence, spin structure and state backreaction. Prove gauge invariance and regulator/mode cutoff convergence. Include receiver feedforward and time-of-flight explicitly.
4. **GR/QFT causality:** use the actual metric's light cones and causal Green function support, timing across spatial exterior vs wormhole, no-superluminal-to-ambient result. A larger *optical or circuit* communication advantage is NOT proof of faster-than-light signalling.
5. **Three driven plasma regions:** compute `δW_ren`, `δJ`, `δ<T_kk>`, and **δquantum channel `S,K,η,F`** from actual Maxwell–plasma fields. Compare balanced C3 drive, amplitude/holonomy modulation, symmetry-broken, nuisance EM pickups. No three balls → monopole assertion.
6. **Optional continuous-variable/multimode track:** compare to Lou et al. by specifying Gaussian/symplectic resources, noise covariance/crosstalk and independently spatially addressable modes, rather than importing qubit success numbers or counting 12/24/27/100 as physically sourced channels.
7. **Horned-sphere PR #1244:** possible nonabelian boundary holonomy/Dirac spectral consumer, not the U1 `H²` magnetic throat; no physical quantum teleportation by horn/VOA analogy.

## Test command and status

```sh
python3 scripts/check_mmp_teleportation_channel_bridge_20261024.py
```

Locally executed equivalent expanded script: PASS. Exact committed reduced checker: source-written, pending reproducible exact-head execution. No kernel-certified Agda teleportation protocol or measured physical wormhole experiment. Prior source authors credited, paper dates and evidence scopes unchanged.
