# Quantum, string and classical spacetime as hyperfabric: finite cut and physical gates

Date: **2026-10-24**. Status: **finite executable exact-arithmetic model PASS**, **Agda source written, no exact-head kernel receipt**, **no physical unification**.
This is a derived investigation from the existing DASHI formalism. Finite Fourier analysis, p-adic mathematics, Hilbert quantum mechanics, differential geometry and worldsheet sigma-models are established external mathematical/physical prior art, not original discoveries in this tranche.

## Canonical owners: don't rebuild the 369 substrate

- 369/27 path hypervoxel: `DASHI/Foundations/Base369Ternary27HypervoxelFabricGeometryExact.agda`, carrier `{-1,0,+1}^3`, **54 undirected path edges**; nine-coordinate aggregate has 3^9=19683 sites.
- Directed signed neutral zero: `DASHI/Foundations/SignedZeroTernaryOrientationExact.agda`, `DASHI/Physics/Closure/SignedZeroTorsionReceipt.agda`: `-0,0,+0` are distinguishable provenance/orientation states, all scalar-zero. Do not interpret as three values of complex quantum amplitude zero.
- Periodic finite characters: `DASHI/Biology/BalancedTernaryFourierModeExact.agda`, `DASHI/Algebra/TriadicDepthOneCharacters.agda`. Their periodic group is `(Z/3Z)^n`, which is **not** the path-graph hypervoxel adjacency.
- Non-Archimedean address/refinement: `DASHI/Codec/TriadicPAdicCodec.agda` and `TriadicPAdicCylinderExact.agda`. Ultrametric refinement is not already a real smooth manifold.
- Contextual zero residual: `DASHI/Cognition/PNF/BracketedTSFVFractranWorldFibreExact.agda`; a neutral coarse observation can retain several admissible worlds and histories.
- Quantum mereology/spacetime: `DASHI/Quantum/QuantumMereologySpacetimePromotionExact.agda`.
- Finite GR and quantum: `docs/concrete_flat_gr_quantum_models.md`; balanced finite (-,+,+,+) flat metric and a trivial joint model, not nonflat quantum gravity.
- Scaling/physical identification: `Docs/papers/PhysicsScalingLimitSpine.md`, `DASHI/Unified/QuantumClassicalGravityBoundaryIntegration.agda`.
- **Existing canonical universal-theory programme**: [dashi_agda PR #1217](https://github.com/chboishabba/dashi_agda/pull/1217), `toe/369-universal-realization`. New work should feed its physical-owner max-cut and should NOT fork a new TOE architecture.
- Relevant selected physical/VOA donors: [PR #1165](https://github.com/chboishabba/dashi_agda/pull/1165) and [C3/Monster/KK PR #1239](https://github.com/chboishabba/dashi_agda/pull/1239). Existing Monster charge charts are not spatial isometries, and finite spectra are not continuum physical particle spectra.

## Delivered exact finite mathematics

1. `DASHI/Unified/HyperfabricSignedZeroWaveGeometryCutExact.agda` reuses the actual signed-zero owner to prove a scalar-zero readout cannot be injective, proves scalar projection invariant under a phase rotation, and imports the existing C3 character translation eigenlaw. It intentionally juxtaposes a path voxel and periodic wave site without equating their operators.
2. `scripts/check_hyperfabric_wave_geometry_cut.py` implements integer-pair arithmetic in the Eisenstein ring `Z[omega]`, `omega^2+omega+1=0`, and checks orthogonality `sum_x chi_k(x)=27 if k=0 else 0`, exact forward/inverse Fourier maps, all three-dimensional periodic eigenlaws, and a **same-label operator counterexample**.
3. The two 27-site graphs differ: `P3^3` has **54** edges, degrees 3 at a corner and 6 at the centre; periodic `C3^3` has **81** edges and constant degree 6. The periodic Fourier modes diagonalize the periodic graph Laplacian, eigenvalues `0,3,6,9`. A nontrivial character fails the path-grid eigen-equation at a corner. The path product instead has one-axis Laplacian eigenvalues `0,1,3`, with 3D eigenvalues equal to three such terms; its first positive eigenvalue is 1 vs 3 for the periodic graph. No automatically justified physical same-operator bridge exists.
4. A 3x3 periodic 2D source grid mapped into three-dimensional integer targets has a squared-gradient toy energy zero for constant maps and positive for an explicit varying map. It is **not** a physical string theory. No physical continuum, real metric, Hilbert norm, Born rule, or GR equation is inferred.

Reproduce the mathematical checks: `python3 scripts/check_hyperfabric_wave_geometry_cut.py`. For formal verification use the repository's pinned Agda 2.9/stdlib runner to check `DASHI/Unified/HyperfabricSignedZeroWaveGeometryCutExact.agda`; NOT executed in this environment (no local Agda executable). A successful Python check is not an Agda kernel receipt.

## What the unified hyperfabric should mathematically mean

Use a compatible diagram of **typed fibres over refinement scale and local physical patch** rather than declaring `3^n` to be spacetime. At depth `d`, a physical candidate `F_d(U)` carries (i) an incidence/cover, (ii) signed-zero orientation and provenance, (iii) fields, operators, observables, (iv) dynamics and compatible restrictions on overlaps, (v) a reference metric and dimensions/normalization when physical, (vi) a controlled coarse graining `F_(d+1) -> F_d`. Pay functoriality and gluing, then prove **commuting squares** with identified continuum physical operators. Formal quantifier order matters: bounds must be uniform in cutoff, not chosen separately per mode.

- **Quantum**: selected complex Hilbert space, *-algebra, states, unitary or quantum-channel evolution, Born probabilities, chosen Hamiltonian and observable-preserving refinement. C3 characters give exact symbolic phases, NOT normalization, positive probabilities, interacting QFT or empirically selected quantum dynamics. `-0/0/+0` belongs to an informational orientation fibre, not three zero-valued physical amplitudes.
- **Classical spacetime**: selected Lorentzian signature, nondegenerate metric, causal structure, connection, curvature, Cauchy evolution, stress from action variation, and validated Newtonian/relativistic limits. An ultrametric ternary address does not fix a Lorentz metric. The repo already gives a valuation/metric underdetermination counterexample.
- **String-like**: a 2D worldsheet `Sigma`, target `M`, embedding `X:Sigma->M`, target and worldsheet metrics, Polyakov/Nambu–Goto action, constraints and gauge/Weyl/BRST conditions as appropriate, physical spectrum/anomaly control, continuum limit and observable matching. A diagram of braids/torii or discrete gradient energy does not pay any of those obligations. Treat Monster/VOA and KK as conditional *candidate* donors, not already identified string spacetime.
- **Semiclassical joining**: for the same metric/field and a specified state, compare stress from the selected QFT with Einstein source via action variation and renormalization. A common 369 index is not a same-physical-object theorem.

## Highest-alpha cross-pollination by consumer

| Consumer | Admissible reuse | Irreducible physical / analytic cost | Priority |
|---|---|---|---|
| Yang–Mills | finite incidence, gauge-link bookkeeping, orientation and chosen lattice operators | nonabelian Wilson/gauge action on **the chosen graph**, gauge-covariant difference, renormalization, **cutoff-uniform** continuum estimates, OS reconstruction and physical mass gap | P1 |
| Navier–Stokes | exact Fourier basis and counterexamples, signed source-ledger, commuting residual squares | actual R3/T3 Fourier operator and quadratic convection; physical R568/R406 signed cutoff-uniform budget and continuation. Graph gap does not prove smoothness | P1 |
| Riemann hypothesis | arithmetic characters, p-adic refinement, ternary signed provenance | equality with the **actual zeta** analytical object and its far-minus-mu signed estimate; no spectral analogy substituted for RH | P2 |
| BSD | p-adic local arithmetic/valuation, explicit prime/address carriers | selected elliptic curve Selmer/Tate-Shafarevich/L-function same-object bridge | P3 |
| Hodge | typed finite cohomology/lattice models | real algebraic cycles on smooth projective varieties recovering rational Hodge classes | P3 |
| P versus NP | radix-neutral encoding and proof/cost receipts | complexity-class preserving polynomial reductions with size/control, no 369 speedup assumption | P4 |
| Poincare / 3-manifolds | topological tests and local/global counterexamples | no new Clay target: classical conjecture solved. Do not promote analogies | support |

**Negative control that should survive every refactor:** `P3^3` periodic-wave interchange must fail without a charged-link/graph-change operator or explicit quantitative residual. It is a small concrete test distinguishing actual wave/discrete operators from a 27-element naming coincidence.

## Phases and executable next cuts

**Phase H0 (this PR):** exact finite zero quotient, Fourier/graph mismatch, worldsheet toy and auditable boundary; Agda exact-head verification still pending.

**Phase H1:** settle *which* Laplacian/dynamics is primary. For original spatial paths derive proper orthogonal eigenfunctions and a complete eigenvalue basis; for periodic theory use C3 Fourier; only claim a shared operator after proving a graph morphism/operator intertwiner, or an explicit convergent family with norm-controlled residual. Preserve signed-zero fibre and noninjectivity.

**Phase H2:** reuse PR #1217 actual source Hilbert/g-TPS/Hamiltonian inhabitants, not new generic `QuantumState` axioms. Pay physical state, Hamiltonian, observable and transition matrix intertwiner on the chosen graph. Add Born/energy conservation tests and comparison to known QFT model before suggesting an empirical novelty.

**Phase H3:** use selected nonflat Einstein/gauge action and metric-stress variation. For string candidates, select an actual worldsheet model and show its constraints/anomalies before talking about spacetime recovery. The recent VOA C27 and KK/braid branches supply *conditional* donors.

**Phase H4:** separately import an identified YM or NS consumer. Target YM source-selected gauge action and cutoff-uniform physical mass, or NS physical R568/R406 operator/estimate. For RH demand actual analytic identity and bound. Do not open a new chain of RNNN wrappers.

**Acceptance discipline:** local arithmetic receipt + exact Agda 2.9 focused receipt + direct source-theorem comparison + physical same-object/intertwiner receipt; release only claims for which all required gates are paid. No new Clay/TOE status is granted by this finite cut.


## Additional same-graph quantum constructor (2026-10-24)

`scripts/check_hyperfabric_path27_quantum_walk.py` (exact rationals, no
floating point) constructs a **genuine finite Hilbert toy on the ORIGINAL
P3^3 adjacency**. One-dimensional real standing modes are

`(1,1,1)`, `(1,0,-1)`, `(1,-2,1)` with graph-Laplacian
eigenvalues `0,1,3` and squared norms `3,2,6`, respectively.
Their tensor products give a full 27-vector orthogonal basis, exact
Fourier-like synthesis/reconstruction, and diagonalize the PATH Laplacian,
not the periodic C3 Laplacian.

For the explicitly **chosen** Hamiltonian `H=L(P3^3)` on
`C^27`, exact real-rational time-`pi` propagation satisfies

`U(pi)=exp(-i*pi*H)=((2/3)J3-I3) tensor ((2/3)J3-I3) tensor ((2/3)J3-I3)`.

This is a real symmetric unitary involution:
`U^dagger U=I` and `U^2=I`. A central-position delta state
evolves to amplitude `-1/27` at the centre and `8/27` at each
corner, giving exactly `1/729` and `64/729` Born probabilities,
respectively. The full probability sum is exactly 1. Exact rational
checks cover 27 eigen-equations, every mode overlap, full completeness,
27x27 orthogonality and evolution of a nonconstant state.

Run: `python3 scripts/check_hyperfabric_path27_quantum_walk.py`.

**Interpretation:** This pays a meaningful *finite same-graph mathematical*
discrete/wave construction. It does NOT pay a unique physical Hamiltonian,
experimental calibration, scaling/continuum QFT, Lorentz causal dynamics,
nontrivial physical strings, or YM/NS/RH Clay consumers.
The P3 and periodic C3 eigenbases each span the same site vector space,
but the two selected Laplace operators differ. Reconciliation means choosing
an operator or paying an operator-valued residual, not confusing the bases.

**Updated phase accounting:** H1's finite-source standing-wave basis and toy
quantum unitary now have a constructive reference calculation. The outstanding
H1 frontier is a **kernel-certified** formalization and a physically
selected/scale-indexed operator comparison. H2 remains real Hamiltonian /
observables identification and physically defensible dynamics, not the
already-solved finite orthogonality calculation.
