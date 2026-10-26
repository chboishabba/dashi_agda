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


## 2026-10-24 27−1 operator and string cross-cut

### Already-owned original source results
- DASHI/Wikimedia/IbrahimTernary27OriginTraceless26AlbertShapeBidiExact.agda proves a TWO-SIDED bijection between the actual 27-site {-1,0,1}^3 path hypervoxel and one selected centre site plus an explicit 26-constructor non-origin site carrier. It expressly does not prove that the selected centre is the Albert identity or that an F4/E6/Jordan product is transported.
- DASHI/Foundations/ExceptionalAlbertFreudenthalResidualExact.agda separately records the actual exceptional Lie/Jordan dimensions Albert 27=1+26, F4 52=26+26, E6 78=52+26 and Freudenthal 56=1+1+27+27. Those representation structures are not thereby the spatial cube.
- DASHI/Wikimedia/IbrahimA027907PathCubeTernaryExceptionalThirteenSnowballExact.agda proves the path-ADJACENCY eigenband multiplicity pattern 1,3,6,7,6,3,1 and 27=1+13+13. Its sqrt(2)-weighted adjacency bands are not the combinatorial GRAPH LAPLACIAN spectrum.

### Newly verified 26-dimensional same-operator chart
Let C={-1,0,1}^3, o=(0,0,0), V=Q^C, L the ordinary undirected path-graph Laplacian. The one-dimensional L kernel is the global constant function, NOT the delta-function at the centre site. The zero-mean subspace V0={f: sum_C f=0} is exactly 26-dimensional and L invariant.
Define q(f)(p)=f(p)-f(o) for non-origin p, and r(a)(o)= -sum(a)/27, r(a)(p)=a(p)-sum(a)/27. They are mutual inverses between V0 and Q^26, while r(q(f))=f-mean(f)*1 on all V. This is a genuine same-operator 26-coordinate identification, NOT Albert-algebra or physical 26D bosonic-string identification.
For D the 26x26 PRINCIPAL origin-deleted matrix of the original 27x27 Laplacian, and b the 26-vector indicating the six original centre neighbours, the true reduced operator is A=qLr = D + 1*b^T. The rank-one term is REQUIRED. D alone is a different Dirichlet-puncture system. The pulled-back inner product is G=I-J/27 and A^T G = G A. The full L tensor eigenvalues are 0,1,2,3,4,5,6,7,9 with multiplicities 1,3,3,4,6,3,3,3,1. The nonzero spectrum is thus 26 modes.

### Separate genuine antipodal 13+13 spectral decomposition
Spatial inversion I(x,y,z)=(-x,-y,-z) preserves actual P3^3 adjacency, fixes only o and pairs exactly 26 nonorigin sites into 13 pairs. Since I and L commute, V0 splits as 13-dimensional inversion-even mean-zero modes plus 13-dimensional inversion-odd modes, both invariant under L. Independent basis candidates are delta_p+delta_-p-2*delta_o and delta_p-delta_-p, one per opposite pair. This is a natural 13+13 MODE decomposition, but its involution parity is NOT string worldsheet chirality, BRST ghost number, physical helicity or the earlier A027907 parity identity merely because the dimension matches.

### Direct implementation and execution
- DASHI/Unified/Hyperfabric27MinusOneAntipodalSameCarrierCutExact.agda now reuses the original spatial point and existing Ibrahim scalar+26 bijection to prove antipodal involution, unique fixed origin and exact preservation of all three types of path-grid adjacency. It also imports the earlier 26=2*13 and exceptional dimension theorem. SOURCE-WRITTEN and exact-head AGDA KERNEL UNVERIFIED.
- scripts/check_hyperfabric_27_minus_1_operator_cut.py adds exact Fraction checks of 26x26 q/r identities, D-vs-A defect, G-adjointness on all basis pairs, all 27 wave eigenmodes and orthogonality, and 13+13 inversion preservation. An equivalent file ran locally and every printed PASS check succeeded; no Agda, Lean or CI executed.

### Critical interpretation / no promotion
Twenty-six non-origin SITES, 26 graph nonconstant MODES, a 26-dimensional traceless ALBERT representation, 26 bosonic target DIMENSIONS and conformal matter charge c=26 are independent typed consumers. The bosonic no-ghost calculation 24+2-26=0 belongs to selected Monster VOA plus II(1,1) plus bc ghosts; the conventional lightcone reduction D-2=24 concerns physical transverse oscillator polarizations after constraints, NOT deleting two spatial cube sites. The TEN-dimensional RNS/CY branch c10+5-26+11=0 is yet another distinct construction. Retain signed-zero fine orientation: remove a chosen scalar wave mode, not an arbitrary sign/zero provenance state.

### Max-cut next tasks
Phase H1 (finite): kernel-certify qLr=A, G positivity and G-adjointness and the 13+13 inversion-eigenspace decomposition using canonical 27 graph and existing theorem owner. Avoid replacing the original owner's source provenance.
Phase H2 (selected matter): compare the ACTUAL selected 369 Coulomb/Monster/VOA Hamiltonians with A, not just shared size. A positive physical bridge needs matching eigenvalues, commutators/vertex modes, inner product, time evolution, observables and a genuine action-preserving map; negative result should record a quantified residual.
Phase H3 (string): test the published Borcherds actual physical-state/BRST construction or a separate selected RNS model with its own worldsheet action, normal ordering, modularity and anomaly. Do not infer a 26D string from the 27-1 chart.
Phase H4 (YM/NS/RH etc.): only consume this math if it attaches to each original source-specific operator and preserves physically required continuum cut-off estimates or analytic objects; otherwise leave unchanged.


## 2026-10-24 sourced physical 27D -> 26D membrane/string / Albert research lineage

### PRIMARY source roots and exactly what each establishes
- Gary T. Horowitz and Leonard Susskind, 'Bosonic M Theory' (2000 arXiv:hep-th/0012037; journal DOI 10.1063/1.1376160). ORIGINAL PROPOSAL, not theorem: a conjectural 27D strong-coupling bosonic M-theory with gravity and a three-form potential, compactified on a LINE INTERVAL to the known critical 26D bosonic string. It is NOT the discrete deletion of one vertex from a 3x3x3 cube, nor does it supply an internal 27-site metric.
- M. Hayakawa and N. Ishibashi, 'Perturbative world-volume dynamics of the bosonic membrane and string' (2001, arXiv:hep-th/0107103). Conditional membrane/background analysis and string double-dimensional reduction; recovers critical D=26 in the analysed Polyakov/Schild string models and suggests 27 for the membrane. The authors explicitly note difficulty selecting a suitable direct membrane background. This is not a proof of 27D bosonic M-theory existence.
- N. D. Lambert and P. C. West, 'Coset Symmetries in Dimensionally Reduced Bosonic String Theory' (2001, arXiv:hep-th/0107209). Source criticism: the naive proposed 27D bosonic M action's reduction did not reproduce the expected coset symmetries; their analysis discusses the dilaton normalization discrepancy 125/121. A model-by-model falsifying consumer is needed, not a free dimensional identity.
- Frank D. Smith Jr, 'Physical Interpretation of the 26 Dimensions of Bosonic String Theory' (2001, arXiv:physics/0102042). ORIGINAL AUTHOR interpretation claims the 26 real dimensions of traceless Albert J3(O)_0 are bosonic string target coordinates, with claimed 4+4+8+8 physical allocation. This is prior speculative work directly aligning with the repo's existing 27=1+26 Albert shape; it is NOT the original mathematical identity of the traceless Albert representation and not a formal or empirical validation of that physical interpretation.
- Horowitz/Susskind 27D interval reduction and Smith 26D Albert identification are DISTINCT 2000/2001 proposals by different authors with different assumed sources. Neither derives the other. The valid algebraic 27=1+26 identity predates both. Borcherds/FLM c=24+2, Weyl/BRST and 26D criticality are separate prior mathematical/quantum facts.

### New explicit constructive classical physical-source cut
The existing DASHI/Physics/Foundations/GRQFTNambuGotoSurfaceActionExact.agda already models a genuine 2+1-dimensional positive-tension membrane/domain-wall action; the previously established 3x3 finite 2D worldsheet kinetic chart uses a distinct 1+1 source geometry. Instead of assuming these are the same, scripts/check_hyperfabric_27_26_wrapped_membrane.py computes the standard CONDITIONAL classical double dimensional reduction. If a membrane worldvolume Sigma2 x S1 wraps once a fixed-radius R, isometric target circle and the induced metric factorizes as h3=h2 (+) R², then det(h3)=R² det(h2), and the area action reduces to the 2D Nambu string action with tension T_string=(2*pi*R)*T_membrane. The original Nambu worldvolume stress and this wrapped-circle worldvolume are both 3-dimensional, but the wrapped embedding, ambient 27D target fields and source stress have NOT been identified.
The checker tests 135 selected rational Lorentzian (1+1) metrics and three sample KK-connection shifts per metric with exact determinants; all cases pass. If the KK shift is included inconsistently (offdiagonal without the matching quadratic block), the apparent simple reduction fails; with the proper horizontal metric adjustment, block determinant remains compatible. This is a meaningful positive/negative metric/source test, not the Horowitz/Susskind 27D quantum action or 26D anomaly cancellation. A local equivalent reference script was executed PASS; GitHub-committed file existence verified but the Git blob was NOT byte-executed.

### Strong mathematical / physical discriminator
The source-selected graph-mode quotient carries the POSITIVE-DEFINITE metric G=I-J/27 with 26 real/rational coordinate amplitudes. Because (sum a)^2 <=26 sum(a_i^2), one gets a^T G a >= (1/27) sum(a_i^2)>0 for nonzero a. Thus this G cannot itself be the Lorentzian string target-space metric of signature (1,25). An independently selected indefinite form, representation and action must be supplied before describing the graph-mode coordinates as target spacetime. Similarly the traceless Albert J3(O)_0's standard compact/F4 trace form is not automatically a 26D Minkowski metric. Structural similarity cannot pay this metric mismatch.
Original source links: https://arxiv.org/abs/hep-th/0012037 ; https://arxiv.org/abs/hep-th/0107103 ; https://arxiv.org/abs/hep-th/0107209 ; https://arxiv.org/abs/physics/0102042 ; https://doi.org/10.1063/1.1376160 .

### Physical phases and Pareto now
B0 completed: historical provenance and two 27->26 interpretations distinguished (27D TARGET compactification vs 27-site CUBE origin removal). Existing Albert 1+26 and Monster c24+2 were found; earlier combinatorial 13+13 and new spectral 13+13 remain distinct operators.
B1 completed as finite computation: true mean-zero 26-mode graph reduction including rank-one repair, exact 2D classical Weyl kinetic density, and conditional classical membrane-circle to string determinant. Agda antipode theorem source-written, not kernel verified.
B2 next theorem: source-select a concrete 27D membrane action with actual Lorentzian target and interval/circle compactification, derive the *literal 26D* string action including correct kinetic/dilaton/B stress factors and compare Lambert-West coset/125-to-121 obstruction. Stop if coefficient mismatch persists; do not call it a full string theory.
B3 separate next theorem: reproduce/assume under clearly attributed boundaries selected bosonic worldsheet Virasoro+bc nilpotence and physical BRST quotient, or choose RNS separately. All 26 bosonic target coordinates must be from selected X-maps/fields, NOT from 26 hypervoxel labels.
B4 optional physical identification: same-object 26D target, Albert Jordan product/F4 and original hyperfabric 26-mode operator. Require an equivariant Lorentz-causal action, matching inner products, dynamics, energy/stress, physical observables and controlled continuum limit. A positive-definite 26-graph-wave operator cannot be declared Minkowski without metric conversion and independent action.
B5 all Clay connections fail closed until the canonically selected YM/NS/RH operators and original continuum/analytic estimates are attached. No evidence here closes a Clay problem.

## Operator-sensitive compact S1 handoff to KK #1241

Source consumer: [KK/Casimir/QED/QCD #1241](https://github.com/chboishabba/dashi_agda/pull/1241), `Docs/physics/TOEKKQCDCircleSpectralStressBIDIMaxCut20261024.md`. This is a CROSS-BRANCH provenance reference, not a typed import.

Our exact `P3^3→P3^6→P3^9` extends graph axes rather than refining one fixed-dimensional fifth circle: its first nonzero Laplacian eigenvalue remains 1, multiplicity grows 3→6→9; the untwisted smooth S1 first level has degeneracy two. Same 27-site counts do not identify P3^3 (54 edges), C3^3 (81 edges) and C27 (27 edges).

#1241 supplies a physically appropriate *distinct* N=3^k periodic circle lattice, exact Wilson-link gauge covariance, and fixed Fourier-band `O(N^-2)` KK spectral/heat error. Full unbounded Casimir/QCD stress requires an independent regulator-uniform limit. It also rewrites the selected QED+QCD stationary vacuum failure as an uncancelled five-dimensional internal pressure. The new local calculation therefore does NOT upgrade this branch's finite hyperfabric toy to physical KK, Einstein, string or QCD.

Original dimensional deconstruction prior art: Arkani-Hamed, Cohen, Georgi, PRL 86 (2001) 4757, DOI 10.1103/PhysRevLett.86.4757. The sibling physical theorem owners remain independent until merged and typechecked.


## FINAL 2026-10-24 SOURCE-SELECTED ACTION RESULT: DO NOT REBUILD THIS IN A NEW TOE WRAPPER

**Authoritative focused ledger:** `docs/hyperfabric-27-minus-1-physical-action-k27-source-maxcut-20261024.md`.

This new tranche **independently derives** Lambert–West's original `125/121`
dilaton kinetic mismatch for the selected simple 27D Einstein–Hilbert
+ 3-form action under single-circle reduction, instead of merely
recording it as an external source. Exact metric ansatz:
`G_(d+1)=diag(exp(2aσ)g_d, exp(2bσ))`.
Common string-frame exponents for R and H³ force `b=-2a`.
After the conformal scalar curvature and integration by parts:
`K_actual=(d-1)(d-6)a²`, while normalised string-frame
`Phi=-(d-4)aσ/2` requires `K_required=(d-4)²a²`.
The exact gap is `(d−10)a²`; at d=26, ratio
`500/484=125/121`; at d=10, ratio 1. This **falsifies the
literal unmodified selected simple 27D action** as a reduction to
the conventional tree-level 26D bosonic string-frame action.
The stronger and distinct Glennon/West 2024–25 `K27=D24+++`
symmetry/brane/coset comparison remains the next physical owner;
no universal impossibility result asserted.

Exact chosen action *partial success*: constant-radius 27D
`-F4²/(2·4!)` with y-leg potential `C_{μνy}=r B_{μν}`
reduces to 26D `-H3²/12`; 162 exact-rational Lorentzian
backgrounds pass. Its naive extension to variable radius
fails because `d(rB)=rH+dr∧B`. This is a same-source
positive/negative pair—not all Einstein/dilaton physics.

Original path-graph *independent* representation no-go:
`L δ_origin=6δ_origin−sum_neighbor δ`; the origin scalar
line and the 26 non-origin SITE span are not closed under L.
The **different** 26-dimensional mean-zero wave space is invariant
and self-adjoint in positive `G=I-J/27`, with eight distinct
positive eigenvalues. Since the real compact F4 traceless Albert 26
is irreducible, it cannot simultaneously carry this non-scalar,
self-adjoint, F4-equivariant *unchanged* L. A different/symmetry-broken
Hamiltonian is allowed and requires a new physical selected object.

**Source-rooted owners and new receipts**:
- `DASHI/Unified/Hyperfabric27MinusOneOriginalPathInvariantNoGoExact.agda` — original-cube non-origin adjacency no-go, source-written; Agda kernel unverified.
- `scripts/check_hyperfabric_27_26_action_obstruction.py` — exact Git blob `97472debda8443394c09f94b2229396570a481b1`, executed PASS 676 bilinear pairings, eigenspaces and source-path leakage.
- `scripts/check_27d_3form_26d_string_sector.py` — exact Git blob `b40fa7889866ff843ff3343a1bb1aeb48cf26c68`, executed PASS 162 test backgrounds and variable-radion counterexample.
- `scripts/check_27d_bosonic_m_dilaton_125_121.py` — exact Git blob `96f2f1eb91d487b3ddc18acd785ade4261132801`, executed PASS 102 exact rational source coefficients, derived `125/121`.
- Lean #84 `Integration/DASHITOE/BosonicM27CoefficientCut.lean`, exact blob `e3377919e2e3557a6e2bb47f25d7998696a9d98f`, theorem source-written, Lake/kernel unverified.
- External physics roots: Horowitz/Susskind 2000/2001; Lambert/West 2001; Glennon/West 2024/25; Glennon 2025; conventional bosonic tree string-frame action source. Attribution labels the `125/121` as originally published.

**Changed Pareto**: selected original 27D action has a **resolved negative** physical verdict, not a vague open dimensional-comparison question. To proceed toward actual unification, source-select a DIFFERENT K27-preserving action and prove the same target stress, dilaton normalization, gauge/Bianchi, BRST/anomaly and observables. Do not feed finite 26 modes into YM/NS/Clay without the canonical source estimates.


## Follow-on physical same-object result (2026-10-24): scalar repair ≠ 27D K27 theory

The canonical **focused** owner is
`docs/hyperfabric-27-minus-1-physical-action-k27-source-maxcut-20261024.md`.
Do not retell its full source atlas here.

**New A3b exact arithmetic:** supplementing the selected 27D
Einstein–Hilbert+3-form by a new canonically normalized real
`χ` with `-1/2(∂χ)²`, *then imposing* `χ=kσ`
would repair the reduced 26D string-frame coefficient for
`k²=32a²` (`a` the warp normalization), since
`500a²-k²/2=484a²`. This is only an OFF-SHELL
action coefficient. The independent free 27D scalar EOM
`Box_Gχ=0` is not implied by the ansatz; an explicit flat-base
`σ=t` has `Box_Gχ=-22ak exp(-2aσ)≠0` for `a,k≠0`.
No source-authored K27-preserving action or consistent
physical single-scalar truncation was constructed.

**Correction to earlier variable-radius rhetoric:** in the natural
form potential chart `B=C_{..y}`, `F_{...y}=dB`
for variable radius with no extraneous `dr∧B`. The
`dr∧B` term arises from choosing the OPTIONAL rescaled
`C_{..y}=r(x)B`, and invalidates only a naive use of that
rescaled chart. The separate 125/121 dilaton no-go still holds.

**Direct source (K27) owner:** Glennon 2025 §VII explicitly
admits that the proposed E27 commutator at level eight was
not computed. His §VIII argues the E27 field content lacks the
required 22-form dual three-form and dual-graviton fields.
A scalar coefficient patch does not address these symmetry/duality
fields, and “K27 not subalgebra of E27” is an attributed source
argument, not a kernel-certified unconditional Lie-algebra theorem.
The high-value selected consumer is the *known 26D K27
closed-bosonic string* rather than an invented 27D tensor action.

**True Jordan operation source donor:** Lean4 #52 already
implements the original Griess 1990 `F3³` homogeneous Albert product.
For all 26 nonzero `a`, `e_a e_-a=e0`
and `e_a e0=e_a`; the non-unit 26-dimensional homogeneous
span is not a Jordan subalgebra. This operation-level leakage
is distinct from, but a useful *structural comparison* with,
the original Cube27 graph Laplacian's origin/nonorigin coupling.
Preserve original attribution and separate the 54-edge path
graph, 81-edge periodic group, complex Albert Jordan algebra,
physical 26D string target and `K27` Kac–Moody symmetry.

New Agda tests: `scripts/check_27d_scalar_repair_consistency.py`
(510 selected rational checks and wave EOM negative control) and
`scripts/check_27_origin_albert_griess_product_cut.py`
(all 26 source-original Griess unit/opposite identities).
Equivalent local scripts PASSED; committed blob byte-replay
not established. Lean #84 appended source-written formal
scalar-slope and nonzero free-EOM coefficient proofs,
Lean/Lake kernel UNVERIFIED.

**Pareto after the cut:** A3 original no-go done; A3b
arithmetic repair done but dynamical consistency blocked;
A4 K27 algebra/source commutator unverified; A5 actual
Albert multiplication exists in sibling #52, same-operator
physical cross-transport unpaid; retain YM/NS independently.


## Additional literal 26D physical consumer and Monster/M24 split (2026-10-24)

Detailed and provenance-audited source:
`docs/hyperfabric-k27-26d-bfield-22dual-m24-signed-duad-maxcut-20261024.md`.
The 26D `K27` bosonic-string action is the correct selected downstream
rather than an imagined universal 27D string completion:
`d(e^-2Phi *H3)=0` locally yields a **dual 22-form**,
with a nonconstant-dilaton exact B-sector positive fixture
and a **failed** metric Einstein equation for that test source.
The physical 24 transverse closed-string tensor decomposes
`299 symmetric traceless +276 antisymmetric +1 scalar =576`.
This reuses existing Leech (299) and M24 duad (276) owner
counts but **does not identify their physical representations**.

ATLAS 2A/2B character values disprove original M24
**unoriented** duad p276 ~= SO24 antisymmetric physical
B2 as an M24-equivariant map: 36≠20; 12≠−12.
An oriented signed-duad line **does** model Lambda²
and Hodge maps it to Lambda²², but neither actual
Moonshine Tate276 nor signed-zero C3 fibre is thereby
identified. New executable finite 276-basis SO24/ATLAS
tests, sympy local dual B-field tests, and Agda source
class-theorem owner in PR #1249. Kernel unverified.


## 2026-10-24 selected physically nonflat 26D target instead of 27D dimension speculation

See detailed source and executable at
`docs/hyperfabric-k27-26d-su2-nsflux-linear-dilaton-worldsheet-maxcut-20261024.md`.
The standard `R^(1,22)×S³` round SU2 group manifold
with nonzero NS H=(2/r)vol and **spacelike** Phi=x¹/r
satisfies all chosen **leading 26D continuum NSNS field
equations** with genuine nonflat Ricci, nonzero stress,
nonzero dilaton gradient. Exact source curvature using
SU2 bracket and covariant flux EOM executed PASS for six
rational radii. Global B gerbe/flux quantization remains
real, not a single globally defined B2 potential.

Cross-pollination path: original SU2/Spin, GR metric/stress,
Hodge/Bianchi, VOA current-algebra and KK source owners,
without identifying this target SU2 S³ manifold with the
original discrete C3³ hypervoxel or asserting Monster
physical state/action identity. WZW SU2_k finite central
charge `3k/(k+2)` plus 23 flat/one spacelike linear
dilaton requires `alpha'V²=1/(k+2)` for c26,
whereas the uncorrected two-derivative geometric
relation says `1/k` and leaves
`delta c=12/[k(k+2)]`. This is a clear quantum
correction and source-consistent future test.
No direct terminal Clay payment.


## WZW / global gerbe / doubled phase-space late source cut (2026-10-24)

The canonical source dossier
`docs/hyperfabric-k27-26d-su2-nsflux-linear-dilaton-worldsheet-maxcut-20261024.md`
now records source-authorized **global** north/south
S3 B patches, quantized H, and explicit global
C22 on the same actual 26D nonflat NSNS source.
Existing SU2_k integrable CFT source-owner files
`KacMoodyLevelReceipt`,
`SU2Level4Spin1RepReceipt`,
`LevelRankDualityReceipt`, `VertexOperatorAlgebraCore`
and `TwistedModuleModularity` are the available
Agda reuse targets. Source: Michael B. Schulz,
arXiv:1106.6291 (2012): 2D WZW action plus
`TM ⊕ T*M` doubled momentum/winding/string
Hamiltonian; not another numerical 3/6/9 geometry.
Next true hyperfabric bridge: operator-preserving
worldsheet momentum/winding generalized metric
and source B-gerbe patch descent on an *actual*
selected target. No categorical C3→Z2 orientation
homomorphism produces a nontrivial sign:
coprime group orders; U1 B-gerbe is another
distinct higher-gauge object.
The actual nonflat source breaks GLOBAL SO24
even though the FLAT massless state space
has SO24 299+276+1.


## Highest-value source WZW operational patch result

The 2026-10-24 K27/WZW owner now actually checks the
standard Schulz (2012) `TM⊕T*M` worldsheet
Hamiltonian `v^T g v+(p+Bv)^Tg^-1(p+Bv)`
on **both** source-selected SU2 S3 gerbe patches.
Explicit B-transform with
`p_N=p_S-(B_N-B_S)v`
preserves the entire O(3,3) generalized metric
and tangent-cotangent pairing; 6×6 symbolic
identities plus 27 concrete phase-space
examples PASS locally. New source script
`check_k27_wzw_gerbe_od3_hamiltonian.py`,
focused canonical WZW dossier
`docs/hyperfabric-k27-26d-su2-nsflux-linear-dilaton-worldsheet-maxcut-20261024.md`,
and Lean #84 thin rational local patch proofs
SOURCE-WRITTEN/kernel-unverified.

This is the specific classical sigma-model
same-object field/momentum patch construction
previously missing from the generic hyperfabric
roadmap; it is not a 369/27-site graph
equivalence or quantum BRST completion.
Global B patch difference represents
quantized U(1) gerbe data and cannot be removed
by one global gauge 1-form.


## Witten source-owner cutoff (2026-10-24) — third-party original lineage

The repository already contains an extensive “Witten”
programme, but not one single named physical operator:
(1) Witten 1989 Chern–Simons/Jones → chiral
WZW/Verlinde block theory (existing SU2 k levels/k4
integrable source owners);
(2) Witten 2007 proposed Monster c24/AdS3 pure gravity
(existing substantial sibling Agda #1239 J, Virasoro,
C27, braid/SL2Z and conditional gravity source);
(3) Witten SUSY index in QFT master (targets only);
(4) Witten Laplacian in YM master (false/open receipts);
(5) Maloney–Witten 2007 physics adversary for
the gravity saddle sum.

An exact selected Witten 1989 `SU2_4`
Verlinde source ring was run locally:
S²=I, 125 fusion coefficients, 625 fusion
associativity checks, quantum dimensions
1,√3,2,√3,1; Gauss–Milgram framing `i`.
It is **not** the 2007 holomorphic c24 Monster
1-simple-sector modular category (framing1).
Agda+Lean typed/numerical sources committed,
kernel unverified. For details see
`docs/hyperfabric-witten-cs-wzw-monster-ads3-source-maxcut-20261024.md`.

The next string source bridge is the ACTUAL SU2
affine VOA/worldsheet state/BRST/g,H,Φ,gerbe
and worldsheet momentum/winding Hamiltonian,
not another modular/cube label comparison.
Original physical work and attribution to Witten,
FLM, Verlinde, Maloney–Witten retained.


## 2026-10-24 newest-PR cross-pollination/source actual Witten conformal algebra

Primary new canonical D4 owner:
`docs/hyperfabric-witten-d4-conformal-su2-4-su3-1-current-embedding-maxcut-20261024.md`.
Genuine **published 1989** `SU2_4⊂SU3_1`
conformal embedding is an operational
chiral algebra extension linking existing
SU2 k4/CS and SU3 k1/anyon three-fold
owner labels (not a color/geometry theorem).
Source rational `sl2→sl3` matrices have
Dynkin index4, adjoint `3+5`;
source branching `SU3 vacuum→(SU2 0+4)`,
`fundamental,anti→SU2 label2`,
giving exact `D4` partition
`|chi0+chi4|²+2|chi2|²`.
Local exact S/T modular, 27 source
SU3 Verlinde and 81 associativity checks
PASS. The 3 C3 invertible sectors arise
after Z2 boson condensation/extension,
not as original SU2_4 simple currents.

Current unrepaired boundaries: original
horned C3 (especially characteristic3
nonsemisimple) and signed-zero C3 are NOT
SU3_1 braided line categories; Monster
C27→C3 reduction is many-to-one; the
27-site P3³ graph is not the 3D SU3_1
topological CS or quantum worldsheet.
Actual 5D E6 source actions/CS and
Albert trilinear triality residual in newest
PRs #1217/#1241/#1106/Lean #52
cannot be bypassed. The chosen nonflat
SU2 WZW × linear-dilaton 26D string
still needs source full current OPE/BRST
and quantum-to-target gerbe/momentum
transport. New Agda and Lean source proof
modules remain kernel-UNVERIFIED.


## Attached worker's true max-cut integrated into hyperfabric/TOE phase hierarchy

Full independently attributed source and H0–H6 roadmap:
`docs/hyperfabric-horn-witten-su3-regularity-charge-maxcut-20261024.md`.
Worker PR #1247 carries chosen exact
SU3 Wilson trace/interference and
50/50 original test receipt; horn PR
#1244 has Hatcher commutator
regularization probe, literal C3
geometric action and separate nontrivial
A5³⋊C3 finite VOA quotient. This
branch REUSES these sources as external
unmerged evidence rather than importing
the modules or duplicating their operators.

**Strongest maths**: Hatcher perfect
horned-exterior G has `Hom(G,C3)=0`,
even though compact ambient SU3 admits
nontrivial NONABELIAN root holonomy;
source `SU3_1` WZW pointed C3 fusion
labels cannot directly encode horn
meridians. Its external C3 geometric
rotation is a distinct quotient.
Further, nontrivial root
`delta=||W-I||>0` forces nonshrinking
deep unitary holonomy norms
`≥(2delta)^(1/2^n)/2→1/2`;
bounded connection plus uniformly
shrinking actual representative loops
would contradict this. Quantitative
GEOMETRY of the intended three-copy
wild embedding not established.
The original 27-site P3³ graph,
27 spectral Monster C27 labels,
ternary C3 rotation, SU3_1 fusion
charges, SU3 gauge Wilson matrix,
and 26D target WZW worldsheet are
six DIFFERENT objects without an
actual same-operator/state transport.

**Pareto reorder:** physical
horn geometry/regularity now first
within any horn-specific claim;
synthetic gauge-invariant two-path
interference an independent
engineering model with S1/F2
negative controls; source Hosotani
potential only after geometry and
physical matter/boundaries selected;
VOA/SU2_4→SU3_1 embedding can
continue natively but cannot bypass
the topology; 5D KK common
Einstein–Maxwell–matter stress, lepton
anomalies and empirical calibration
still unpaid. No Clay promotion.


## 2026-10-25 stronger NEW geometric max-cut: exact source Wilson norm and diameter countercontrol

Canonically grounded continuation:
`docs/hyperfabric-horn-finite-length-trace-regularity-maxcut-20261025.md`.
**Exact no-eigensolver selected SU3 certificate** from the original
sibling #1247 Q(zeta3) trace:
`ReTr(W)=221179426799/216225930001`;
`||W-I||_op²>= (6-2ReTrW)/3
=854996726408/648677790003 >1`.
This is source arithmetic plus the standard
unitary Frobenius/operator inequality. Thus the
fixed physical representative W would have
delta_op>1 without numerical eigenvalue software.

**Finite-depth no-go rather than only asymptotic**:
the universal commutator envelope
`E_(n+1)(eps)=2(E_n(eps))²` has
`E_n(1/2)=1/2` exactly for EVERY finite n.
If at any complete Hatcher depth all true
holonomy leaves have norm-gap <=1/2,
the selected root delta>1 is impossible.
A concrete analytic source-geometric witness
would be `sup_len_depth(n)=ell_n`,
`sup_compatible_connection_norm=M`,
and `M ell_n<=1/2` with genuinely
matched, whisker-conjugated source generators.
Neither `ell_n` nor M is already certified
for the 3-copy wild exterior; Euclidean
handle *diameters* alone do not supply
path-length bounds.

**Strong new counterexample proving need for LENGTH**:
on smooth Euclidean R², take SU3 gauge
`A=(i diag(1,-1,0)/2)(-y dx + x dy)`
with nonzero bounded constant curvature
and the radius 1/n circle traversed n² times.
Image diameter 2/n->0, pointwise norm
||A|| <=1/(2n)->0, but length=2pi*n,
and holonomy diag(-1,-1,1) at every n.
The original ordinary smooth SU3 gauge
theory is prior art; our concrete exact
high-winding negative control is the new
selected regression. It is NONFLAT
and HIGHLY REPEATED, NOT an actual simple
Hatcher meridian nor a flat-horn countermodel.
Do not infer physical singularity from it.

**New source discrepancy explicitly quarantined:**
Hatcher, *Algebraic Topology* Example 2B.2,
p.172 explicitly states the direct-limit
horn complement is nontrivial with TRIVIAL
abelianization and “highly nonfree”.
The 1968 N. W. Riebe institutional
abstract describes its `G^k` groups as
free countably infinite rank. They cannot
refer to one isomorphic nontrivial marked
group because a free group has nonzero
abelianization; Riebe's full thesis PDF is
access-restricted, so differing spaces/
constructions/abstract wording remain
UNRESOLVED, not an error proved.

**Executed receipt**: new
`scripts/check_horn_geometry_length_trace_maxcut.py`
local source PASS: exact rational trace and
operator-gap bound, 33 exact fixed-depth
envelope checks, numeric consistency for
seven selected depths, seven exact high-winding
negative controls. GitHub committed file exists
and math source is locally reproduced;
**byte-exact Git blob execution is not claimed**.
Lean #84 `HornWittenRegularityAndChargeCut.lean`
appends source-written rational selected
gap/cutoff and radius/winding source lemmas.
Lean/Lake KERNEL UNVERIFIED.

**True Pareto** is to construct/verify an
actual source MARKED meridian loop family
with unitary whisker/basepoint compatibility,
controlled tube clearance and rigorous
metric *length* bounds (or exhibit a
nonshrinking escape), before promoting
any horn-specific Witten/Neutrino/KK
physical claims. D4 SU2_4⊂SU3_1 and
Hatcher's perfect group no-abelian
charge map remain independent mathematical
constraints; no new CS, Monster, Clay or
experiment theorem is paid by this regression.


## 2026-10-25 final horn/Witten source correction and highest-alpha frontier

Canonical focused owner: https://github.com/chboishabba/dashi_agda/blob/chatgpt/hyperfabric-wave-spacetime-cut-20261024/docs/hyperfabric-horn-a5-flat-bundle-onebranch-maxcut-20261025.md

Historical owners: Hatcher's Alexander horn fundamental group; independent Agda horn #1244 owns the nontrivial A5 quotient and finite c=0 VOA; independent Agda neutrino/Wilson #1247 owns the selected noncentral W. Standard icosahedral A5 and flat-principal-bundle monodromy reconstruction are published prior mathematics.

A new finite-image theorem gives a strictly stronger geometric filter for the A5 quotient: every nonidentity element of the standard faithful icosahedral A5 < SO3 < SU3 has operator-gap at least sqrt((5-sqrt5)/2)>1. A nontrivial root commutator forces both children nontrivial recursively, hence ONE sequence of genuinely marked descendant meridians with lengths tending to zero contradicts a compatible uniformly bounded FLAT connection realizing that finite-image representation. This is NOT the unrestricted SU3 result, which required a stronger full-depth small-leaf condition.

A positive independent result is also necessary: the nontrivial representation of the classical Hatcher exterior's pi1 into SU3 automatically yields a smooth FLAT SU3 principal bundle with that holonomy on the OPEN exterior via the standard universal-cover construction. It need not have connection coefficients uniformly bounded near the excluded wild boundary. Thus abstract smooth-flat existence is positive, and the physical regularity requirement is the live issue. The SU3 principal bundle over this 3-manifold is topologically trivial by standard low-dimensional obstruction theory.

Three genuine exact source regressions have passed locally with byte-for-byte Git blob hash verification:
(A) A5 60 elements / 3600 commutator pairs / 8 synthetic collar stages / 127 topological parent-child WINDING mismatch controls; Git blob bce4f345d18912687bcf2d4a99d469376db39754.
(B) smooth FLAT punctured-plane order-five single winding loops, shrinking length and connection coefficient norm growing as 1/r; Git blob b15a80bc228f213f3918c2fd3509499034620f34.
(C) smooth bounded NONFLAT SU3 on simply connected R2 with different Wilson holonomies on homotopic contractible loops; Git blob 4876fffbcc823aebf929c6b0bd6ef29b42591ece.

The synthetic geometric collar is explicitly NOT Hatcher marked: each of 127 parent circles has child-core winding (1,0) versus (0,0) for the required commutator, proving a literal topological rejection instead of a decorative failure flag.

The selected separate #1247 W has nonzero imaginary trace because its exact zeta3 coefficient is nonzero. Every element, and every SU3 conjugate, of the chosen REAL icosahedral A5 < SO3 subgroup has real trace. Thus W cannot be identified with the A5-root holonomy in that representation. The original two selected math programmes must remain separately typed.

MOST IMPORTANT PHYSICAL PRECONDITION: Hatcher's pi1 relation between meridians implies a relation between holonomies automatically ONLY for FLAT monodromy representations. With nonflat connection, Wilson holonomy depends on the geometric representative; a controlled non-Abelian Stokes/homotopy/curvature-defect estimate is essential. Earlier loose wording about arbitrary bounded nonflat connections is superseded. The original FlatFormalDiskHolonomySurface mathematical interface owns the unresolved Stokes/analytic terms.

Lean #84 adds SOURCE-WRITTEN generic all-descendant-nontrivial, one-short-marked-descendant/finite-gap contradiction and selected Wilson nonreal trace certificate. Lean/Lake and Agda kernels not run; no actual source-coordinate three-copy Hatcher collars or uniform physical connection, no Witten/Monster/TOE identification and no Clay theorem.

Current Pareto: construct genuinely linked Hatcher Z-block collars with van Kampen parent-as-commutator marking, collar clearance, arclength and compatible whisker/gauge data for ONE descending branch; if that exists, the finite A5 uniformly bounded flat realization fails. For general curved gauge fields, separately quantify homotopy-surface curvature defects.

## 2026-10-25 worker attribution correction: W infinite order ALREADY belongs to #1247

The strongest finite-image exclusion is NOT a new original #1249 discovery. Agda sibling #1247 already owns `NeutrinoExistingCPFiniteResidualNoGoExact.agda` and its exact Galois-trace certificate `442358853598/216225930001` in (2,3), with the standard algebraic-integer theorem stated as an external prerequisite. Original `NeutrinoHornedExteriorFifthPowerNoGoExact.agda` additionally owns the specific A5 fifth-power transfer. Our #1249 reproduces the exact rational certificate and adds the *independent* Q(zeta3) field norm `34895555697482945411132133124/33067970309429875820893367281` in (1,2). This second noninteger norm corroborates the original mathematical W-INFINITE-ORDER conclusion, ruling out ALL finite-image group representations of the selected W; it does not pretend to be first to that theorem.

The original Agda horn #1244 A5 quotient/c0 VOA remains a separate positive finite-image construction. A new complete 60/60 A5 inverse-conjugacy witness proves all unitary A5 characters real and also rejects the nonreal-trace W; this narrower result is strictly SUBSUMED by the original infinite-order no-go. Exact Agda #1249 scripts source-written and byte-for-byte locally executed, source hashes `b4a23effa02df27fe66c5e001f88f057cec3c8ea` and `4cb2aaf316ed28207d66a5f516c9d8bbbddeb30d`.

The correct positive compact-SU3 distinction: infinite order does NOT give a positive identity gap for all nontrivial powers. Standard two-eigenphase Dirichlet recurrence proves for all Q≥2 some m≤Q² with `||W^m-I||op≤4π/Q`; selected source W shows `||W^458-I||op≈0.04449169165` in a NUMERICAL regression (six Q values). Committed/equal blob `5de01046b58a8bd73fb9ac0681e9576b0a930619`. The finite A5 one-short-branch obstruction does NOT transfer to this W; the general full-depth commutator envelope remains conditional on FLAT source holonomy and true marked geometric lengths.

The Hatcher p171 source `Z` marking is once-punctured-torus boundary word `[a,b]`; the new exact finite free-group word test checks eight substitutions (2^n generators, 4^n nontrivial reduced word, zero abelianization), and rejects the original synthetic unlinked tube mark by its nonzero winding. Source executable blob `7a73fc6d68f55105de93ee416798f59127c03391` locally byte-tested. This is topological COMBINATORIAL marking, not a linked 3D Z-block coordinate/metric proof. Next actual producer remains a geometric marked meridian/collar with all-stage complement clearance, lengths and whisker compatibility, or a rigorous counterexample.

Canonical new source and stage roadmap:
`docs/hyperfabric-wilson-infinite-order-eisenstein-source-maxcut-20261025.md`.
Lean #84 `Integration/DASHITOE/HornWilsonInfiniteOrderEisensteinNormCut.lean` source-writes the distinct field-norm certificate, exact trace ranges and generic ambivalent-character lemma, with number-theory integrality as an explicitly identified standard external premise. **Lean/Lake kernel UNVERIFIED**. No observed lepton/TOE/Monster/Clay result.


## 2026-10-25 sharper Hatcher one-branch SU3 theorem: 2^n rather than 4^n

**New canonical source/implementation:** docs/hyperfabric-horn-onefastbranch-sharp-unitary-maxcut-20261025.md and scripts/check_horn_single_fast_branch_unitary_cut.py in Agda #1249; Integration/DASHITOE/HornSingleFastBranchUnitaryCut.lean in Lean #84. Original Hatcher Example 2B.2 (printed pp.171–172), original horn A5/VOA #1244, original selected W/noninteger trace #1247 and existing FlatFormalDiskHolonomySurface retain authorship/ownership.

For any UNITARY A,B, the elementary exact identity ||[A,B]-I||op=||AB-BA||op gives the stronger d([A,B])<=2 min(d(A),d(B)); previous valid bound 2 d(A)d(B) <=4d(A) is nonoptimal for a chosen child. Thus for ANY selected TRUE FLAT Hatcher horn group representation G→SU3, and ANY one depth-n descendant w, d(Uroot)<=2^n d(Uw). Given a genuinely source-marked local meridian length L_w and compatible uniform connection bound M, d(Uroot)<=2^n M L_w. Exact previously checked selected W source character certifies d(W)>1. Therefore ANY chosen depth with 2^n M L_w<=1 contradicts W, without finite-image or full-depth-smallness assumptions. A geometrically marked path shrinking as L0*q^n with q<1/2 and M bounded would settle the bounded-FLAT-selected-W case conditionally. **Source-true linked marked geometry and loop LENGTH are STILL UNPROVED**; do not promote Hatcher's topological picture into metric q<1/2.

Exact local rational rates for hypothetical M=100,L0=1: q=1/8 depth4, q=1/5 depth6, q=1/4 depth7, q=1/3 depth12; q>=1/2 gives no crossing. Additional heterogenous *complete* binary tree certificate 2 d(root)<=∏(2 epsilon_leaf), checked across nine exact test trees, complements one-branch criterion. Agda Python reference PASS; current remote Git script exists. Lean new native theorem source conditional on explicit normed-commutator/flatness premises, **Lean/Lake kernel UNVERIFIED**.

For CURVED connections, π1 group relations do not imply equality of Wilson matrices on homotopic loops unless a curvature/homotopy (non-Abelian Stokes) error is controlled; a genuine literal loop concatenation is another possible source but must match the independently selected root loop. No claim of actual linked three-dimensional Z-block, Witten/Monster/TOE source action or Clay estimate.
