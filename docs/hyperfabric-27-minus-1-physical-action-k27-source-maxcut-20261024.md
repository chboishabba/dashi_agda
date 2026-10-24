# 27 − 1: same-action adversarial cut (hypervoxel / Albert / 26D string)

Date: 2026-10-24. Branch of Agda PR #1249; cross-prover companion Lean PR #84.
This is a **source-selective physical and mathematical test**, not a proposal
that dimensional coincidence identifies physical theories.

## Primary authority and sources (historical order)

* **Original Albert/F4 representation**: the real octonionic Albert Jordan algebra
  `J3(O)` has dimension 27, with scalar identity and its 26-dimensional
  trace-zero complement. The latter is an irreducible representation of
  compact `F4 = Aut(J3(O))`, equipped with an invariant trace form.
  Distinguish `dim V=26` from a 26-dimensional Lorentzian TARGET manifold.
  Source: [Cacciatori et al., Mapping the geometry of F4](https://intlpress.com/api/bgcloud-front/resource/pdf/volume/1805561993266405378-1805561993266405378-c735a8e8c459c8ab62e7c4217685ae4b.pdf),
  §2; [Humphreys on real F4 26](https://mathoverflow.net/questions/95982/type-of-26-dimensional-representation-of-different-real-forms-of-the-complex-sim/96477).
* **Horowitz & Susskind**, [*Bosonic M Theory*](https://arxiv.org/abs/hep-th/0012037)
  (2000, J. Math. Phys. 2001): conjectured 27D target-space gravity + a
  three-form action, compactified on `S1/Z2` interval to the 26D bosonic
  string. It is explicitly a conjecture, not a source proof.
* **Hayakawa & Ishibashi**, [*Perturbative world-volume dynamics of the
  bosonic membrane and string*](https://arxiv.org/abs/hep-th/0107103)
  (Nucl. Phys. B614, 2001): world-volume membrane/special reductions to
  Polyakov and Schild string models; 26D critical string / 27D membrane
  argument **does not supply a known suitable direct membrane background**.
* **Lambert & West**, [*Coset symmetries in dimensionally reduced bosonic
  string theory*](https://arxiv.org/abs/hep-th/0107209)
  (Nucl. Phys. B615, 2001), §4: source-specified dilaton kinetic mismatch
  by factor `125/121` and failure of expected reduced coset symmetry for
  the proposed 27D action. This is an EXTERNAL paper assertion, not a
  computed result of the DASHI 27-site graph.
* **Glennon & West**, [*`K27` as a symmetry of closed bosonic strings and
  branes*](https://arxiv.org/abs/2409.08649)
  (Int. J. Mod. Phys. A40, 2450155, 2025): very-extended
  `K27 = D24+++` representation reproduces the 26D closed bosonic
  string low-energy effective action including brane contributions.
  **K27** here is an infinite-dimensional Kac–Moody algebra label, NOT the
  27-site Cartesian cube, nor the 27D bosonic M target by definition.
* **Keith Glennon**, [*Bosonic M-Theory from a Kac–Moody Algebra
  Perspective*](https://arxiv.org/abs/2501.03000) (2025):
  argues the Horowitz–Susskind 27D circle/`S1/Z2` uplift fails to protect
  the required `K27` symmetries and that **no obvious** 27D bosonic M
  extension exists within the studied algebraic route. Not a universal
  impossibility theorem for every conceivable action.
* **Standard closed-string low-energy string-frame source**:
  `S26 ∝ ∫ d26x sqrt(-g) e^(-2φ)
  ( R[g] + 4|∇φ|² − H_{μνρ}H^{μνρ}/12 )`;
  see [EPJ C 81 (2021)](https://link.springer.com/article/10.1140/epjc/s10052-021-09518-6).
  Stress, frame, gauge, dilaton normalization and overall units are part
  of the selected physical theory.

## Original repository mathematical owners

1. `DASHI/Wikimedia/IbrahimTernary27OriginTraceless26AlbertShapeBidiExact.agda`
   already proves a **bijection of sets**
   `Cube27 ≅ {origin} ⊎ 26 non-origin points` with both round trips and
   maps origin to a scalar-labelled summand. Does NOT transport the
   octonionic Jordan product or F4 action.
2. `DASHI/Foundations/ExceptionalAlbertFreudenthalResidualExact.agda`
   already provides proper 27=1+26, 52=26+26, 78=52+26, 54→53 and
   56-dimensional Freudenthal shape plus same-action requirements.
3. `scripts/check_hyperfabric_27_minus_1_operator_cut.py`
   already implements the **different** invariant zero-mean graph-wave quotient.
   In its original origin-difference basis, the true operator is
   `A=D+1*b^T`, not the principal Dirichlet submatrix D. Positive
   `G=I-J/27`, 26 path eigenmodes, antipodal 13+13.
4. `DASHI/Unified/Hyperfabric27MinusOneAntipodalSameCarrierCutExact.agda`
   already proves the original cube's fixed-origin antipodal adjacency
   symmetry and consumes the original 1+26 chart.
5. `DASHI/Physics/Foundations/GRQFTNambuGotoSurfaceActionExact.agda`
   already gives **2+1 membrane** domain-wall stress. The wrapped membrane
   test in `scripts/check_hyperfabric_27_26_wrapped_membrane.py`
   verifies a conditional membrane->1+1 string tension, but does not
   identify a 27D source action or a 26D string spectrum.
6. `DASHI/Moonshine/VNaturalOrbifoldConstruction.agda`,
   `MoonshineMonsterLieStringBigradingExact.agda` and
   `TwistedModuleModularity.agda` own the c24 Monster / Lorentzian
   lattice / no-ghost and worldsheet VOA input boundaries.
   Their 24+2−26 central-charge arithmetic belongs to a distinct
   published bosonic chiral construction.

## New exact tests on ORIGINAL selected operators

### (A) Direct 27-site origin scalar != invariant under its own dynamics

Exact graph Laplacian `L` on original `P3^3` has:

```
L δ_origin = 6 δ_origin − sum_{six original neighbours q} δ_q.
L 1 = 0.
L δ_(1,0,0) evaluated at origin = −1.
```

Therefore **both** the one-dimensional span of the centre-site basis vector
and the 26-dimensional span of NONORIGIN site basis vectors fail to be
L-invariant. Reusing the existing Albert-shaped *set bijection* as a
*linear dynamical* Albert `scalar ⊕ traceless` representation would
therefore lose the original adjacency operator.

Instead, the mean-zero quotient `V0 = {f : sum f=0}` **is** L-invariant,
with true origin-difference operator `A=D+1*b^T`, and positive-definite
`G=I−J/27`. It has **eight different positive eigenvalues**
`1,2,3,4,5,6,7,9` with multiplicities `3,3,4,6,3,3,3,1`,
and inversion splits `13+13` nonconstant modes. The origin-complement
and constant-complement decompositions are different and not equivalent
without a nontrivial change of coordinates/operators.

NEW Agda source proof:
`DASHI/Unified/Hyperfabric27MinusOneOriginalPathInvariantNoGoExact.agda`
consumes original Cube27 and the exact earlier chart, and constructs a
path witness `positiveX → origin`, refuting an adjacency-closed
non-origin sector. Agda kernel NOT run.

NEW independent exact-rational executable:
`scripts/check_hyperfabric_27_26_action_obstruction.py`.
**Exact Git blob `97472debda8443394c09f94b2229396570a481b1`
executed locally** on all 676 basis inner-product pairings; all checks
passed. Spectral decomposition and origin-neighbour witnesses passed.

### (B) Conditional F4 no-go, not an irrelevant numerical coincidence

The real compact Albert traceless-26 representation is an **irreducible**
`F4` representation. If the original 26-dimensional G-self-adjoint
graph operator `A` were *also exactly F4 equivariant on the same
irreducible real representation*, every eigenspace of A would be a
nonzero F4-invariant subspace. Irreducibility then forces
`A=lambda*identity`. It is NOT scalar (eight positive eigenvalues).
Hence the triple

```
exact original Cube27 path L (after zero-mode quotient)
+ full compact irreducible F4 on same 26D linear space
+ isometric, dynamics-preserving F4 intertwiner
```

is mathematically impossible.

**Allowed alternative**: an F4 action does not preserve that same L;
or explicitly broken/reduced symmetry; or replace L by an F4-equivariant
operator (scalar on that irreducible module); or select a larger/reducible
representation. **Not ruled out**: F4-equivariant interactions on other
fields, the scalar+traceless Albert Jordan algebra itself, or different
string worldsheet Hamiltonians. No nontrivial F4 action on our
26 graph modes has been constructed here.

### (C) Genuine chosen 27D four-form term -> 26D B-field term (partial positive)

Fix 27D spacetime `M26 × S1`, constant radius `r>0`,
block `G27=diag(g26,r²)`, circle coordinate `y` with period `2π`,
no y dependence and one electric 4-form polarisation. Let
`C_{mu nu y} = r B_{mu nu}` (a CONSTANT-r redefinition), and
`F4=dC3`, `H3=dB2`. Then exactly:

```
F_{mu nu rho y} = r H_{mu nu rho}.
F4^2 = 4 H3^2       (because G^yy=r^(-2) and four positions for y).
−F4^2 / (2 * 4!) = −H3^2 / 12.
sqrt(−det G27) = r sqrt(−det g26).
integral_(0,2π) dy = 2π, so the 26D coefficient is multiplied by 2πr.
```

This is an honest selected **component of a candidate low-energy
27D gravity + 3-form action**, with correct H-sector normalization
under declared assumptions, not just the membrane area determinant.
The all-terms Einstein/dilaton, radion, Kalb–Ramond gauge action and
nonlinear `K27` coset covariance do NOT follow.

NEW executable: `scripts/check_27d_3form_26d_string_sector.py`.
**Exact Git blob `b40fa7889866ff843ff3343a1bb1aeb48cf26c68`
executed locally**, 162 exact rational Lorentzian 27D diagonal
backgrounds, all passed.

**Critical counterexample**: if `r=r(x)` varies and
`C_{mu nu y}=r(x) B_{mu nu}`, then
`F_{mu nu rho y}=r H_{mu nu rho}+(dr∧B)_{mu nu rho}`.
For a constant B12 and nonzero time derivative of r, H012=0
yet F012y≠0. Thus the constant-r field redefinition is NOT a
free dynamical-radion argument, and is in tension with separately
unpaid gauge and dilaton coupling obligations.

### (D) Literal physical action acceptance or reject

**Target theory (string frame, 26D)**:
`S26 ∝ ∫ sqrt(-g) e^{-2φ}(R+4(dφ)^2−H^2/12)`.

**Candidate owner**: Horowitz/Susskind 27D gravity + 3form
low-energy action, with interval `S1/Z2`, boundary conditions,
orbifold parity, graviton/dilaton/two-form/three-form modes and
chosen canonical field frames. The above circle calculation tests
only the local electric 4-form term, not the global interval theory.

**Hard physical witness**: reproduce the *dynamical* scalar kinetic
coefficient and 3-form coupling from the 27D action, including the
correct field frame, 26D units and scalar potential/kinetic
normalization. Lambert/West's source-reported scalar coefficient
ratio `125/121 ≠ 1` is a **negative selected-source regression**,
not a number manufactured by our script. The user's physical
claims should fail if the ratio remains different.

**Strongest consumer**: reproduce/preserve Glennon/West `K27`
symmetry of the chosen closed bosonic string including the dual
form and coset/T-duality restrictions. Glennon (2025) argues
the simple Horowitz/Susskind 27D uplift cannot pass this and that
no straightforward full 27D `K27` extension was found.
Do not label this external observation a mathematical theorem
that every 27D alternative theory is impossible.

**STOP conditions**: action source unavailable; unequal
dilaton/3-form ratios in matched frames; failure to preserve
required gauge symmetry, negative/ghost physical states, anomaly,
or no common geometry/observer. Never promote equality of
hypervoxel cardinality, Albert dimension, central charge,
Dynkin node count or target coordinates to a physical identity.

## Updated phase/DAG, Pareto ordered

- **A0 DONE** — source genealogy + inequivalent 27−1 (site, wave,
  Albert, 27D string target, K27 algebra) identity audit.
- **A1 DONE at finite maths** — positive zero-mean 26 wave action
  + origin-site noninvariance + conditional F4 irreducibility no-go.
  New Agda *source written* proof of path nonclosure, kernel pending.
- **A2 PARTIALLY POSITIVE** — 27D selected 4-form -> canonical 26D
  `H²/12` at constant radius, 162 rational cases, counterexample
  to naive radion lift. Existing wrapped membrane comparison retained.
- **A3 PHYSICAL FIRST BLOCKER** — full dynamical 27D action reduction
  with source frame and interval parity; literal 26D dilaton
  coefficient 125/121 vs target 1, 3-form and kinetic action checks.
  If mismatch cannot be repaired while preserving K27, report a NO-GO
  for this **selected action**, not universal string impossibility.
- **A4 PHYSICAL SECOND BLOCKER** — actual K27 non-linear
  realization/coset symmetry and T-duality/dual field structures;
  source-specific field/metric/observable intertwiner. Use the
  published 2024–2025 literature, not guessed algebra from 369.
- **A5 CONDITIONAL** — chosen F4/Albert Jordan product and
  permitted *different* dynamics/symmetry breaking with Lorentzian
  target metric (the original G is positive). If full irreducible
  F4 + original path L is demanded, stop at mathematical no-go.
- **A6 OPTIONAL** — full quantum string BRST, modular anomaly,
  physical Hilbert and empirical low-energy observables. Yang–Mills,
  Navier–Stokes, RH and other Clay source estimates remain on their
  original theorem owners; this cut proves none.

**Certification:** checked local exact arithmetic on precisely the GitHub
source blobs above, verified Git object SHA-1 via Git blob framing;
Agda kernel, Lean/Lake, full continuum action and physical/Clay
promotion NOT checked/claimed.
