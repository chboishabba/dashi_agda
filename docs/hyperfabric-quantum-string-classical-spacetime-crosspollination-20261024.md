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


## 2026-10-24 cross-repo max-cut recut (Agda + Lean4 exact-head archaeology)

### The FOUR inequivalent uses of 27/729

Do not conflate these different concrete mathematical objects:

1. **Spatial Cube27**: `Ternary27Point = {-1,0,1}^3`, exactly **27 points/sites** and 54 nearest-neighbour edges on `P3^3`. See merged Agda #656, #666 and canonical `Base369Ternary27HypervoxelFabricGeometryExact`.
2. **Relational T^27**: Agda #1133 constructs **27 ternary coordinates**, not 27 states/sites. There are `3^27` ambient states; its **policy-completed** global section carries `T^18` free coordinates, `3^18` states, with a selected C3 structural completion. Its exact graph sheaf, effective higher-stack, groupoid and finite hypersheaf are already source-written in the owning sibling, but remain distinct from a physical spatial hypercubic graph.
3. **729 = 3^6**: two spatial Cube27 factors have **729 pairs**. The separately sourced GF(3^6), Monster-3B X6 Heisenberg representation **degree 729**, and Schrödinger model also have size/dimension 729 but are not canonically the spatial pair graph or a Monster VOA eigenspace without a map preserving multiplication and action. Agda #1105 gives an ATLAS-derived *selected* GF729 linear operator/intertwiner by executable finite conjugacy, not a global Monster physical representation. `729*90=65610` counts the selected zeta-sector BASIS LABELS after recognition, not every vector of a 65610-dimensional linear space.
4. **Monster C27 charge chart, PR #1239**: the *original spatial 27 sites* are an explicitly chosen address chart for 27 cyclic charge eigenvalues on actual `V^natural_2` (dimension 196884). Source-reported eigenvalue ranks 7298 at charge zero, 7295 for primitive order 3, 7296 for order 9, 7290 for order 27; sum is 196884. Every original spatial nearest-neighbour bond changes chosen charge; an uncharged block-diagonal hop cannot represent it. **Onsite full-weight-two VOA at each site** and **one VOA partitioned among differently charged sites** are separate candidate theories. The charged vertex link `V^natural` mode remains an actual same-object open producer; neither chart yields an AdS3 dual or physical string automatically.

`T^9` in the base three-cube interaction/appraisal product contains `3^9=19683` states. Its number matches the separate *three spatial Cube27-factor* path product explored in this PR, but the roles/factorizations must be identified rather than coerced by cardinality.

### Additional mathematical operator realization (new in PR #1249)

`scripts/check_hyperfabric_27_729_19683_refinement.py` tests the **actual original path graph** `P3^n` for `n=3,6,9`. Write `L_n` for its combinatorial graph Laplacian, `I_{k,n}f(x,y)=f(x)` for pullback across added ternary coordinates, and `R_{n,k}F(x)=3^{-(n-k)} sum_y F(x,y)` for averaging. For k=3,n=6 and k=6,n=9, exact arithmetic verifies

```text
R I = id
L_n I = I L_k
R L_n = L_k R
```

on every site, for nonseparable test fields on the fine lattice as well as arbitrary selected coarse test fields. The identity follows from **a product graph and the new-axis constant zero mode / cancellation of summed edge terms**; it is a principled mathematical coarse/fine commuting-square, NOT a physical spatial renormalisation theorem. Operator-level free cylinder consistency is stronger than equal cardinalities.

**Negative control:** change one family of new-direction links to sign `-1` (a toy flat-charge transport obstruction). The constant fine field has naive averaged twisted Laplacian `4/3` at every coarse site, while the coarse ordinary Laplacian of its mean is zero:

```text
R L_twisted I(1) = 4/3   !=   L_coarse R I(1) = 0.
```

Thus an actual physical gauge connection needs a connection-compatible section/restriction or an explicit residual, not naive scalar averaging. The differing periodic C3 versus path P3 Laplacians and the Monster C27 charged-edge no-go remain **independent** obstructions, not redundant copies of this one.

**Reproduction**: `python3 scripts/check_hyperfabric_27_729_19683_refinement.py`; exact rational/integer checks are not Agda kernel theorems. Mathematical identity extends to arbitrary finite product paths by elementary edge cancellation, but a general Agda/Lean proof and its source-physical attachment are separate deliveries.

### Cross-repository theorem archaeology (not generic claims of incompleteness)

| Lane / authoritative owner | Actual available constructions at declared scope | Primitive same-object frontier |
|---|---|---|
| **369 and T27 relational geometry** — Agda #1133 | exact policy-completed `T^27` graph, 18 free trits, sheaf/presheaf, groupoid, higher-stack/hypersheaf, native C3 and non-descent of hidden policies | spatial Cube27-to-T27 **typed** representation and physical action compatibility; not new sheaf scaffolding |
| **729/Monster** — Agda #1105, #1162, #1239; Lean #47 | GF729 primitive selected action executable; group/character/projector and generic FDRep/isotypic/Hom compilers; 27-charge multiplicity arithmetic and original-cube edge no-go | actual same-grade VOA fixed-zeta `H_zeta` and `W_zeta` linear action and chosen-phase character transport, `Hom_E` normalizer lifts, physical vertex/gauge links, physical state/action |
| **Quantum mereology** — Agda #1208; Lean #61, #76 | finite heterogeneous TPS/marginals, source g-TPS, finite HS projections and metric formulas (per source author), physical Hamiltonian **example** in Agda #1217/Lean #80 | same physical selected Hilbert/state/g-TPS/Hamiltonian and operational observables; minimizer pullback, thermodynamic limit, nontrivial continuum and same-state holographic gravity |
| **GR & holography** — Agda #898, #905 and flat-GR owners; Lean #68 | intrinsic curvature/causal boundary interfaces, finite flat mostly-plus model, corrected **independent Bell tree** RT equality, nonempty full-domain **flat Lambda=0 Jacobson** benchmark, units calibration | real smooth same-causal-spacetime and sourced *nonflat* Einstein-matter solution with QFT stress, backreaction, matter sourcing; RT benchmark does not imply AdS/CFT |
| **KK and string-adjacent** — Agda #1239, #1241, #1248 | five-dimensional reduction and radion/source/Casimir **candidate** models, selected negative controls, separate independent Maxwell photon; VOA modular/defect, finite C27 charge and braids | physical worldsheet `(Sigma,h,X,g,B,Phi)`, Polyakov/Nambu–Goto dynamics, Weyl/BRST/anomaly conditions, modular consistency, string spectrum, compactification/vacuum and same-observable 4D match. 5D KK ≠ automatically critical string theory |
| **YM** — merged #1230, #1233; open #1165; TOE #1217/#80 | canonical CMP109 residual classification, finite gauge/RG/Hamiltonian compilers and conditional source-Native R457/R131 compilers | real pinned Yang–Mills construction and CMP109 source histories, R114/R119/R122/R124/R127 literal stress/OS semantics, continuum reflection-positive source, **cutoff-uniform physical mass gap**. Graph discrete spectral gap cannot substitute |
| **NS** — merged #1233, #1234; main canonical A/B/C/D scheduler | A/B decomposition and exact non-vacuous B4 R440 analytic interface; existing R406/resolvent/Luo source machinery | B4 physical signed cutoff-uniform R440 inequality and continuation, and A same-object physical Fourier identification/domination; no 27-site P3 Laplacian implies 3D unrestricted smoothness |
| **RH** — Agda #1211 and RH source owners | zero-free, fourth-harmonic and Riemann signed quartic target infrastructure | actual zeta analytic same-object and required signed far-minus-mu estimate; neither finite C3 characters nor Eisenstein lattice counting prove RH |
| **BSD / arithmetic** — Agda #1006; Lean #69/#73 | genuine Eisenstein norm, `j=0` CM point-group action, inert prime local factor and generic split Jacobi compiler | selected split cubic character certificate, primary Jacobi trace, Hecke/Groessencharacter Euler factors; actual Selmer/Ш and BSD rank formula still separate |
| **Hodge / P!=NP** — Agda #1006/#1129 and other existing owners | finite Hodge/geometry and complexity proof grammar; reductions; P9 quotation frontier | primitive algebraic-cycle lift on an actual smooth projective variety; for P!=NP actual resource-valid lower bound, not complexity of representation alone |

**Source status discipline:** PR #1230, #1233, #1234 are merged on master; PR #1133, #1105, #1162, #1165, #1217, #1239, #1241, #1248 are separate open Agda branches; #47, #61, #68, #69, #76, #80 remain separate Lean4 branches where confirmed. Do not treat open branch sources as merged imports or imported Agda formal-source rows as local Lean proof terms, or vice versa. Native Agda/Lean exact-head kernel runs were not performed as part of this PR.

### Max-cut phases and deliverables — avoid a new ontology

| Phase | Deliverable | Acceptance / falsification | State |
|---|---|---|---|
| **0: genealogy & disambiguation** | 27 spatial vs 27 *trits* vs GF729 vs Monster-C27 chart with exact repo/branch owners | no cardinality-to-action coercion; preserve signed-zero fine fibre, p-adic non-Archimedean distinction | source-audited in roadmap |
| **1: finite same-operator bridge** | original P3^3 standing-wave basis, `C^{27}` path-graph quantum walk and `P3^3→P3^6→P3^9` average/pullback | exact eigenbasis/unitary, `RI=id`, both Laplacian squares; periodic/path counterexample and twisted-link `4/3` no-go | exact Python reference calculations; Agda kernel not verified |
| **2: selected SAME physical realization** | link the actual chosen Hamiltonian/state and operator of PR #1217/#80 to the path/periodic/729 representation and observables | source-selected Hamiltonian, amplitudes & Born probabilities, matrix-element action intertwiner; reject if mismatch | unpaid; do not create a replacement generic QFT layer |
| **3: quantum/spacetime/string branches** | from one selected physical action, attach metric/causal boundary, stress, and where warranted a worldsheet/action; leverage Lean #68/#76 and Agda #1165/#1241 donors | *nonflat* Einstein matter; same-state QFT stress/backreaction; for string, real Weyl/BRST/modular/target-spectrum and controlled low-energy limit | selected finite/flat/conditional models exist; full same-action realization unpaid |
| **4: productive Clay BIDI** | feed physical operator maps directly into canonical YM & NS theorem owners, arithmetic maps only into RH/BSD/Hodge/P≠NP when relevant | YM cutoff-uniform selected OS/mass gap; NS physical A/B/B4/continuation; RH actual signed estimate etc | open at listed primitive leaves; no wholesale new theorem wrapper chain |
| **5: scientific discrimination** | chosen held-out observables / limit control / source calibration and comparison to standard effective models | independently replayable source-tied data, alternative-model comparison, physical units and errors | no universal empirical claim |

**Pareto:** mathematical next task is to *formally* certify the currently exact Python `P3^3→P3^6` Laplacian commuting squares and twisted-link counterexample using existing path/hypervoxel owners. The **physical** next task is NOT a new 729-dimensional encoding: test whether the literal selected interacting quantum 369 Hamiltonian and actual Monster grade-two operators admit the required edge/charge/observable intertwiner. In parallel attack canonical YM source physical gap and NS B4/A, not artificial cross-domain analogies. String worldsheet remains a clearly separate, conditional branch.


### Gauge-theoretic correction and positive repair (exact file checked 2026-10-24)

The previously reported uniform `-1` sign on the `(-1,0)` edges of one added axis is **pure gauge** on the entire cubical product. Define a site sign `g(y)=+1` when the selected added coordinate is `-1`, and `g(y)=-1` when it is `0` or `+1`. Then the twisted operator is *conjugate* to the ordinary one:

```text
L_A = G L G,     G^2 = 1.
I_A f(x,y) = g(y) f(x)
R_A F(x) = (1/27) sum_y g(y) F(x,y).
R_A I_A = id;       L_A I_A = I_A L_coarse;
R_A L_A = L_coarse R_A.
```

The naive mean's nonzero `4/3` defect in that gauge therefore diagnoses **gauge-unsafe averaging**, NOT physical curvature. The **corrected covariant projection repairs it exactly**. This is a material improvement on the simple noncommuting diagram.

A separately selected *single negative edge* around a genuine 4-edge square in `P3^6` has a `Z2` plaquette Wilson product `-1`, gauge invariant under every vertex sign redefinition. The updated executable exhaustively tests all `2^4` sign assignments on that square and shows none defines a nonzero global parallel sign section. This is an actual lattice gauge holonomy/flatness obstruction (for the declared discrete `Z2` model), **not a selected interacting SU(2) Yang-Mills construction, continuum field strength, mass gap or string anomaly**.

The committed script `scripts/check_hyperfabric_27_729_19683_refinement.py` has been independently executed in the local container at its **exact Git blob** `e9c2e52af6d986b8aa584ea3f3f5f875a7e14a0b` and reports:

```text
PASS P3^3 <-> P3^6: RI=1, L I=I L, R L=L R, exact
PASS P3^6 <-> P3^9: RI=1, L I=I L, R L=L R, exact
PASS sign-twisted added-edge obstruction: naive R L_A != L R, defect=4/3
PASS flat Z2 twist: covariant I_A/R_A restore both exact Laplacian squares
PASS nontrivial Z2 plaquette holonomy -1: no global nonzero parallel sign section
BOUNDARY free graph operators only; selected physical gauge/GR/string/YM/NS remains unpaid
```

This numerical/exhaustive exact finite fixture tests concrete fields and loop assignments; the general all-fields product graph identity is justified mathematically by `L_(X×Y)=L_X⊗I+I⊗L_Y`, `L_Y 1=0` and `sum_y L_Y F(x,y)=0` from undirected edge-pair cancellation. Kernel certification of a general formal theorem remains separately open. Highest next formal cut: lift the positive flat gauge transport and negative Wilson-loop no-section counterexample into the *existing* selected discrete gauge/path operators rather than installing another formal-claim wrapper.


### Second prior-art correction: nonflat finite GR, Nambu–Goto membrane, Calabi–Yau (2026-10-24)

The earlier shorthand "only flat-GR / 2D toy worldsheet" **undercounted existing merged source work**. Correct it with these canonical files from `master`, individually inspected:

- `DASHI/Geometry/NonconstantWarpedLorentzianModel.agda` computes a **three-time-slice nonconstant FLRW-like signed metric**, metric-derived connection coefficients and nonzero curvature in exact finite symbolic coefficients. `DASHI/Physics/Closure/DiscreteWarpedEinsteinMatterModel.agda` gives a nonzero stress component, an associated matter-action variation table, finite Einstein-tensor/stress matching and a discrete Bianchi/continuity residual. `DASHI/Physics/Closure/CausalNonconstantGeometryRegression.agda` directly checks metric change, metric compatibility, torsion-free coefficients, nonzero source, matched Einstein tensor, and conservation. **This is more than flat vacuum, but not a smooth continuum Einstein-matter solution.**
- `DASHI/Geometry/GeneralLeviCivitaTheoremBoundary.agda` has the general theorem schema and a uniqueness *eliminator conditional on a supplied Koszul determination witness*. It explicitly marks general existence and internal Koszul derivation unproved. `DASHI/Physics/Closure/ContinuumEinsteinMatterSolutionBoundary.agda` proves the **conditional conservation consequence** of an Einstein equality and contracted Bianchi, but marks smooth existence, wellposedness and physical sourcing unproved. `DASHI/Physics/Closure/ContinuumCurvatureSourceSpinTwo.agda` already owns the exact required discrete-to-continuum Ricci/Einstein convergence data as a demanding contract.
- `DASHI/Physics/Foundations/GRQFTNambuGotoSurfaceActionExact.agda` gives an actual symbolic positive-tension **2+1-dimensional membrane/domain-wall worldvolume** action `S=-tau int d^3xi sqrt(-h)`, with exact `P=-sigma`, and `GRQFTNambuGotoRepulsiveBubbleMaxCutExact.agda` composes finite Israel/vacuum/stress fixtures conditional on a normalized CMP119 tensor. This is physically relevant p-brane/induced-metric/stress machinery; it is **NOT** the 1+1-dimensional string worldsheet or a Polyakov 2D quantum theory. The actual YM action generating the wall potential/source is still explicitly open.
- `DASHI/Geometry/CalabiYau.agda` defines a typed structural CY authority (complex/Kähler, c1 zero, holomorphic volume). `CalabiYau369CompactFibreBridge.agda` gives a real **3+6=9 spatial, plus time = 10-dimensional** interpretation and a separate fibre bundle/integration interface; cardinal and dimensional 369 readings remain disjoint. `CalabiYauAnalysisAndPhysicalUseBoundary.agda` and `CalabiYauPhysicalProducerCutset.agda` already enumerate compactness, Yau/Ricci-flat metric, moduli stabilization, reduction, anomaly, low-energy spectrum/couplings and empirical observables. They **do not** automatically construct a concrete stabilized physical CY compactification.
- `DASHI/Moonshine/VertexOperatorAlgebraCore.agda` and `GradedVertexOperatorAlgebraBoundary.agda` already distinguish full VOA vacuum, Virasoro/Jacobi locality/modes from finite graded traces and modular character arithmetic. The model in `TrivialRationalGradedVertexAlgebraExact.agda` is genuinely a trivial VOA example, not the full Monster VOA or a worldsheet quantum string model.

**Corrected phase accounting:** H3 classical GR has an actual *nonflat finite* source-matched benchmark and a separate flat continuum-benchmark in Lean #68; the frontier is now the continuum/same-action/sourced nonflat physical solution, NOT elementary nonflat finite-model existence. H3 strings has a concrete positive-tension Nambu membrane and typed 10D CY dimensional/fibre reduction ladder; the frontier is the **selected 2D string worldsheet**, worldsheet constraints, quantum conformal anomaly/BRST, exact selected physical compactification and matching of string spectrum/low-energy effective stress. This distinction is source-rooted: the membrane and CY records must not be cited as already discharging full string theory.


### Concrete Agda cross-owner theorem imports (no abstraction factory)

`DASHI/Unified/HyperfabricGRStringExistingDonorWeldExact.agda` is now SOURCE-WRITTEN as the one thin compile-facing integration owner. It imports canonical `master` modules and re-exports only:
- actual `NonconstantWarpedLorentzianModel.computedPositiveCurvature`;
- actual 16-component `DiscreteWarpedEinsteinMatterModel.computedEinsteinEqualsMatterStress`;
- actual nonzero `DiscreteWarpedEinsteinMatterModel.computedMatterSourceNonzero`;
- actual `GRQFTNambuGotoSurfaceActionExact.fixtureDomainWallEquationOfState`;
- actual `CalabiYau369CompactFibreBridge.canonicalDimension369` spacetime dimension `=10`.

This is an **already-owned finite theorem connection**, not a proof of continuum GR, Einstein/QFT same-action physics, or a 2D string. The new file has not received an Agda exact-head kernel receipt in this environment; use the repository-pinned Agda runner on the new owner as the acceptance gate. No selected Monster 729 action or smooth manifold data is manufactured by these imports.


## 2026-10-24 source-first STRING / 2D WEYL / MONSTER / RNS max-cut correction

**Critical correction to earlier research summary:** There is already extensive genuine prior art relevant to worldsheet conformal physics in the **master** Agda tree and in separate open sibling PRs. This section audits that work before deciding the remaining theorem producer. It does not pretend that a typed worldsheet-target **interface** is a constructed quantum CFT or that the physical CFT/BRST machinery is absent merely because no file is named `PolyakovWorldsheet.agda`.

### Existing actual source owners, ordered by mathematical authority

| Original current owner | Already constructed/source-written content | What it does **not** by itself prove |
|---|---|---|
| `DASHI/Moonshine/VertexOperatorAlgebraCore.agda` | graded state, vertex modes, vacuum, conformal vector, locality, Jacobi, Virasoro **typed obligations**, mode/group-action and character interfaces | an actual nontrivial full `V^natural` VOA or worldsheet quantum model |
| `DASHI/Moonshine/GradedVertexOperatorAlgebraBoundary.agda`; `MonsterGradedVOABridgeExact.agda` | graded-trace/dimension identity given a supplied group-equivariant VOA with trace data; strong separation of graded representations vs vertex algebra | full VOA construction, analytic modularity or genus-zero from traces alone |
| `DASHI/Moonshine/TrivialRationalGradedVertexAlgebraExact.agda` | concrete **c=0** rational one-dimensional vertex-algebra seed: vacuum, selected modes, creation, translation, commutative associative (-1)-product, zero conformal action | full `V^natural`, physical string CFT, or general VOA Jacobi proof |
| `DASHI/Moonshine/VNaturalOrbifoldConstruction.agda` | proof-relevant FLM Leech `V_Lambda^+ ⊕ (V_Lambda^T)^+` fixed/twisted summands, explicit selected `centralCharge24` and locality/Jacobi assembly requirements | unconditional construction of `V^natural` without inhabited external source/assembly fields |
| `DASHI/Moonshine/TwistedModuleModularity.agda` | source-native commuting-pair `S:(g,h)↦(h,g^-1)`, `T:(g,h)↦(g,gh)`, twisted-sector/traces and *conditional* SL2Z covariance/projective multiplier interfaces | construction of all analytic twisted traces and projective modular action |
| `DASHI/Biology/MoonshineMonsterLieStringBigradingExact.agda` | genuine finite Borcherds root-prefix arithmetic `c(mn)`: `1,0,196884,21493760` on selected (m,n); exact stage ordering through VOA ⊗ Lorentzian lattice → physical BRST quotient → Lie bracket → denominator | actual selected positive physical-state BRST cohomology and complete denominator identity from finite prefix alone |
| `DASHI/Moonshine/RankOneHeisenbergFockWindowExact.agda` and existing rank-one Fock grading owners | exact finite creation/annihilation and truncated commutator/number eigenvectors | completed Fock module, Virasoro/OPE normal-ordering on all modes |
| `DASHI/Physics/QFT/VOAMoonshineBridgeReceiptSurface.agda` | K3 sigma/SCFT, chiral CFT net, full holomorphic factorisation and 4D extraction **target surfaces** with explicit open obligations | nontrivial K3 compactification or genuine 2D quantum sigma model (this module also has postulates: do not promote it into a safe theorem) |
| Agda #1239 (`docs/monster-c24-virasoro-primary-ads3-maxcut.md`, `docs/monster-ads3-gravity-witten-kk-braid-maxcut.md`) | exact finite q-series and selected primary/descendant subtraction, braid/SL2Z representation tests and explicit AdS3/Witten proposal authority | full Monster CFT unitary modular functor or proved AdS3 Einstein gravity dual |
| `DASHI/Physics/Foundations/GRQFTNambuGotoSurfaceActionExact.agda` | actual **2+1D MEMBRANE** positive-tension domain-wall stress law, with source-matching conditional Israel bubble model | **1+1D STRING** Polyakov quantum worldsheet, Weyl criticality |
| `DASHI/Geometry/CalabiYau369CompactFibreBridge.agda`, `CalabiYauPhysicalProducerCutset.agda` | typed **3+6+1 =10 target dimensional** reading, CY structural geometry, compactification/physical anomaly and spectrum contracts | nontrivial selected Ricci-flat compactification, consistent 10D RNS string spectrum |
| `DASHI/Physics/Closure/DarkDimensionStringPromotionBoundaryExact.agda` | source-attributed observational/swamp-land/KK dark-dimension model with empirically falsifiable vs framework-identification split | a proof of string-theory origin or necessary dark-dimension consequence |

**Disambiguate Weyl before borrowing it:** an E8/Coxeter *Weyl group*, a finite qutrit/Weyl (Heisenberg) unitary pair and **local 2D worldsheet Weyl metric rescaling** are different objects. Similarly Virasoro/algebraic vertex actions, quantum consistency of the worldsheet path integral, and Brown–Henneaux *AdS3 boundary CFT* are related via potential translations but are not definitionally the same sector.

### Two precise conformal-charge paths (published PRIOR theory, not DASHI discoveries)

1. **Borcherds/Moonshine bosonic chiral construction**: standard `V^natural` (c=24) and rank-2 Lorentzian even lattice `II_{1,1}` (c=2) form **matter c=26**; ordinary bosonic reparametrization `bc` ghosts have c=-26. Their **signed anomaly budget** is `24+2-26=0`. This is the correct *matter/ghost* prerequisite for the source's no-ghost/physical-state construction; the published theorem is older external mathematics. It does not mean the physical spatial hypervoxel must have 26 sites or that the 27 Monster charges are 26 target dimensions. Source: Borcherds, *Monstrous moonshine and monstrous Lie superalgebras*, Invent. Math. 109 (1992), DOI 10.1007/BF01232032; original author PDF https://math.berkeley.edu/~reb/papers/monster/monster.pdf .
2. **10D RNS (superstring) construction**: 10 free bosons contribute c=10; 10 worldsheet Majorana partners contribute c=5; reparametrization ghosts c=-26 and superghosts `beta,gamma` c=+11. The independent signed condition is `10+5-26+11=0`. The CY candidate's 9 spatial+time=10 label fits the *dimension counting* of this second family but supplies NO spin-structure, superconformal current, worldsheet fermion coupling, NS/R sectors, GSO choice, target beta functions, modular invariant spectrum, or compactification. Monster c24 is not simply an extra sector on that ten-dimensional sigma model: `24+10-26=8 !=0` for the naïve bosonic combo. Source: covariant RNS literature, e.g. PTEP 2015 `033B11` and 2025 `033B02`.

**Why the arithmetic does not close BRST:** c_total=0 is a necessary perturbative conformal-anomaly condition within a specified conventional CFT/ghost model; one must still construct the stress OPE/Virasoro algebra, the ghost Fock representation, normal ordering and intercept, nilpotent BRST charge, BRST cohomology positivity/no-ghost theorem under exact hypotheses, sewing/modular consistency, and gauge/anomaly/physical-state operators. The original Borcherds theorem is externally established; this Agda integration does not kernel-reprove it.

### New owner-first exact cut in this PR

- `DASHI/Unified/HyperfabricMonsterBosonicWorldsheetExistingOwnerCutExact.agda` **imports actual earlier** `VNaturalOrbifoldConstruction`, `MoonshineMonsterLieStringBigradingExact`, and `CalabiYau369CompactFibreBridge`; proves the ordinary exact signed-charge *magnitude* equations `24+2=26`, `10+5+11=26` with explicit provenance; consumes the already-owned `(1,1)` and `(1,2)` Monster Lie coefficient theorems; proves `24+10 !=26` by constructor contradiction; requires the chosen Vnatural `centralCharge24` source input rather than constructing it. Agda file is **source-written, kernel-UNVERIFIED**.
- `scripts/check_monster_bosonic_worldsheet_conformal_cut.py` gives a **nontrivial 2D classical Polyakov-kinetic-density** finite test, not just a 2D embedding sketch. On the existing periodic `C3×C3` nine-site source sheet choose `X(i,j)=(i-1,j-1,((i+j)%3)-1)` in the original **27-site path Cube27 target**, with local positive conformal metric `h_ab(x)=w(x)^2 diag(4,9)`. For discrete forward gradients and finite local area/inverse metric,

  ```text
  sqrt(det h) = 6 w(x)^2
  h^(11) = 1 / (4 w(x)^2)
  h^(22) = 1 / (9 w(x)^2)
  sqrt(det h) (h^(11)|d1X|^2 + h^(22)|d2X|^2)
    = 6 (|d1X|^2 /4 + |d2X|^2 /9).
  ```

  Therefore the **classical kinetic density at each site** is invariant under independent positive local scale changes `w(x)`; exact rational calculation gives a positive total sample `S=78`. This is an exact *2D conformal cancellation* for that selected discretization, not full diffeomorphism invariance, a continuum `∫Sigma sqrt(h) h^ab ∂X∂X` limit, a true dynamic worldsheet metric, or the quantum Weyl anomaly. A membrane `p+1=3` kinetic density would scale as `w^(3-2)=w`, showing why the existing positive-tension membrane cannot be silently substituted. Note also that Nambu-Goto **area** is not invariant under arbitrary rescaling of the *induced* metric; the Polyakov intrinsic 2D auxiliary metric has the separate classical Weyl redundancy.
- A local **equivalent exact-rational replay** of the source-shaped 9-cell worldsheet calculations passed with `S=78` and both critical-charge identities, as well as the prior finite Monster Lie multiplicities. This is **not** an Agda/Lake kernel receipt, or confirmation of a full quantum worldsheet. The branch script has not been independently fetched and run byte-for-byte in this session.

### Updated Pareto max-cut for string theory without inventing another framework

**S0: repository archaeological freeze — done.** Canonical current owners mapped. Worldsheet, conformal VOA, orbifold/twisted modularity, Monster Lie/no-ghost, 10D CY, RNS, membrane, KK, AdS3 CFT and empirical source claims are explicitly separated by theory and provenance.

**S1: finite positive/negative tests — DONE at exact finite arithmetic.** Actual 9-site 2D Weyl kinetic-density fixture into the true Cube27; independent c26 bosonic-Monster and c15 RNS worldsheet accounting; fails the naïve `c=24 + 10` bosonic amalgam. Implemented in same existing hyperfabric PR. New Agda file needs exact-head kernel certification.

**S2: choose ONE **source-owned** quantum string construction before further formalization.** Best already-near term is **Borcherds c24+2 bosonic**: instantiate physical `V^natural⊗V_{II1,1}` and the actual *published* no-ghost theorem through existing `VNaturalOrbifoldConstruction`, `TwistedModuleModularity`, `MoonshineMonsterLieStringBigradingExact` and `VertexOperatorAlgebraCore`. Target the genuine state/VOA restriction and physical-state quotient on the SAME carriers; cannot close with c-number or finite root prefixes alone. **Do not conflate** with selected physical 369 Coulomb Hilbert space, Monster 27-charge chart or the 3x3 spatial paths.

**S3: decide 2D worldsheet physical target.** If selected is the 10D RNS/CY route, derive actual `X:Sigma→M`, worldsheet spin/fermion/super-Virasoro and bc/beta-gamma, GSO and modular consistency with a selected 10D target/CY stabilization. This is not the same job as the Bosonic Moonshine no-ghost theorem; record a **separate** theorem lane, not a hybrid constructed from counting.

**S4: selected QFT/GR/AdS3 and gauge consumers.** Use common stress/action and metric owners from Agda #1165, nonflat finite GR, Lean #68 flat benchmark; for AdS3 Witten's conjectural Monster dual require bulk state/action/saddle/partition and marked boundary modular observable. For YM require real continuum pinned construction/OS/mass gap, for NS physical signed estimate and continuation. No string result can be turned into Clay by a common colour/charge label.

**S5: empirical/discriminating predictions.** Source-chosen observables, dimensional normalizations, unitary+positive physical Hilbert space, anomaly absence, measured spectra/couplings or gravity benchmark, alternative-model comparisons. Reuse #1241 KK and #897 Dark Dimension **bounded tests** only where a selected string compactification actually produces their fields.

**Top theorem leaf:** Not `24+2=26` or `Polyakov density is 2D-scale invariant` (both elementary). It is the *actual physical state/BRST cohomology representation* with an explicit same-object map from the existing Monster VOA/II11 and an operator-preserving comparison to the intended 369 or 4D physical consumer. If the source's physical output is only a mathematically meaningful Monster Lie algebra rather than a four-dimensional observed theory, explicitly report that narrower success.
