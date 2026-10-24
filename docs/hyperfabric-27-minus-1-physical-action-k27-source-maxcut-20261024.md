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


## A3 MATHEMATICALLY RESOLVED FOR THE SELECTED SIMPLE 27D ACTION: DERIVED 125/121

**Material advance**: the earlier roadmap labelled Lambert–West 125/121 an
externally sourced comparison. The branch now **derives it exactly** from the
27D Einstein–Hilbert + one-circle-polarized four-form classical ansatz.
External discovery/priority and originality remain with Horowitz–Susskind,
Lambert–West and later Glennon/West; DASHI implements independent exact
coefficient diagnostics and the same-object boundary. This is a
**source-matched negative result for one definite action**, not a new
in-principle no-go for all possible 27D theories.

Take total spacetime dimension `D=d+1` and metric

```text
ds²_(d+1) = exp(2aσ) g_{μν} dx^μ dx^ν + exp(2bσ)dy² .
```

The fields are y-independent, and only the y-legged 27D four-form
component contributes to the 26D three-form `H3`. Set KK vector and
additional non-electric components to zero. The dimensional density
prefactors after contracting inverse metrics are

```text
EH:  exp(P_R σ),  P_R = (d-2)a + b.
H3:  exp(P_H σ),  P_H = (d-6)a - b.
P_R=P_H iff b=-2a. Common exponent P=(d-4)a.
The source string-frame dilaton then satisfies Phi=-(d-4)a σ/2.
```

For `R_(d+1)`, a conformal transformation of a one-dimensional
warped-product metric yields **before integration by parts**

```text
R_(d+1) = exp(-2aσ) [
   R_d
   - 2 (b+(d-1)a) Box_g σ
   - (2b²+2(d-2)ab+(d-1)(d-2)a²) |dσ|_g² ].
```

After multiplying by `sqrt(-G)` and integrating `Box_g σ` with
weight `exp(P_R σ)`, the kinetic scalar coefficient is exactly

```text
K = (d-1)a [(d-2)a + 2b].
b = -2a ⇒ K_actual = (d-1)(d-6)a².
Standard 26D string-frame action requires
K_required = 4 (dPhi/dσ)² = (d-4)² a².
K_actual − K_required = (d-10)a².
```

At `d=26`, `a=1`, `b=-2`: `P_R=P_H=22`,
`K_actual=25*20=500`; `K_required=22²=484`.
Therefore `500/484=125/121`, *exactly the Lambert–West
source-observed dilaton error*. At `d=10`, both are `36`,
which explains this obstruction's striking 10D-versus-26D split.
This ratio is insensitive to rescaling the auxiliary scalar σ when
the common prefactor `exp(-2Phi)` is held fixed. A different
field content/action, higher derivatives, independent scalar, or
nontrivial symmetry structure **may** evade it but then requires
an honest new source action and a new K27/physical comparison.

### Exact execution and typed Lean source

New original reference executable:
`scripts/check_27d_bosonic_m_dilaton_125_121.py`, exact Git blob
`96f2f1eb91d487b3ddc18acd785ade4261132801`
(run locally, git-blob hash independently matched):
102 exact rational `(d,a,b)` comparisons PASS;
`K_actual−K_required=(d−10)a²` PASS;
`d=26` ratio `125/121` PASS; `d=10` ratio 1 PASS;
common R/H prefactor condition `b=-2a` PASS.

Cross-repo Lean PR #84 adds
`Integration/DASHITOE/BosonicM27CoefficientCut.lean`,
Git blob `e3377919e2e3557a6e2bb47f25d7998696a9d98f`.
It source-writes ring/linear-arithmetic proofs of the full general
dimension identity, the common-exponent restriction, the 26D ratio
and 10D success. **Lean/Lake kernel NOT RUN** in this environment;
the **geometric Ricci scalar transformation is a documented premise**
of the finite coefficient algebra, not itself constructed as an
analytic Lorentz-manifold theorem in that Lean file.

### Revised roadmap impact

- **A3 classical bosonic M proposal**: the source-selected simple
  EH+4form action now FAILS its literal full 26D string-frame
  dilaton normalization test by 125/121, with a derived formula,
  not just an external citation. Physical promotion stops for
  *that specified unmodified action*. The H3 kinetic term alone
  still has a genuine constant-radius positive truncation.
- **A4 alternative action**: a new concrete 27D physical field
  content, metric ansatz, form coupling, K27 invariance and
  anomalies must be source-selected and produce an exact
  no-mismatch reduction; distinguish Glennon's *no obvious
  K27-preserving extension* from an absolute impossibility.
- **A5 hyperfabric/Albert**: independently no exact original
  path-L/H `F4`-equivariant irreducible identification; these
  are different model changes. Changing the string action
  does not automatically repair the F4 path symmetry obstruction.
- **A6 downstream Clay**: no direct payment, since this is a
  negative constraint on one higher-dimensional effective
  action, not a uniform YM or NS continuum theorem.


## 2026-10-24 follow-on maximal cut: coefficient repair vs 27D FIELD DYNAMICS and K27

**SOURCE-FIRST correction:** this section supersedes any loose reading that a
radion-dependent `dr∧B` is **inevitable** in dimensional reduction.
Natural target B-form `B_{μν}=C_{μν y}` has `H=dB` even
for varying radius (the metric's inverse-radius prefactor still varies).
The alternative *field redefinition* `C_{μν y}=r(x)B_{μν}`
induces `F_{μνρy}=rH_{μνρ}+(dr∧B)_{μνρ}`.
Our prior variable-r counterexample proves only that the latter
rescaling cannot be used without its derivative compensation. The
independent **125/121 dilaton coefficient mismatch remains** under
the natural unrescaled component identification; it did not rely on
`dr∧B`.

### Exact attempted minimal correction: an additional 27D scalar

Start with the previously selected `D=d+1` action schematic

```text
S = ∫ d^(d+1)x sqrt(-G) [ R(G) - F4²/(2*4!) ],
G = exp(2aσ) g_d ⊕ exp(2bσ) dy²,  b = -2a.
```

A NEW minimally coupled real 27D scalar `χ` with canonical
source `-1/2 |dχ|_G²` is a physically DIFFERENT theory.
The formal one-field ansatz `χ=kσ` would shift the reduced scalar
kinetic coefficient by `-k²/2` in the common string-frame measure:

```text
K_old = (d-1)(d-6)a²,
K_target=(d-4)²a²,
k² = 2(K_old-K_target) = 2(d-10)a².
At d=26: k² = 32 a² (k=±4 sqrt(2) a over the reals).
Then 500a² - 16a² = 484a².
At d=10: k=0; at d<10 no real k for a≠0.
```

**Strong epistemic boundary:** this is an off-shell ACTION COEFFICIENT
repair, NOT a known 27D consistent single-scalar truncation, a physical
source action or a `K27` invariant uplift. In particular, the independent
free 27D scalar EOM still requires `Box_G χ=0`. With `χ=kσ`,

```text
Box_G χ = k exp(-2aσ)
          [ Box_g σ + ((d-2)a+b) |dσ|_g² ].
```

For `d=26,a=1,b=-2`, selected flat g and `σ=t`,
`Box_g σ=0`, `|dσ|²_g=-1`: thus
`Box_G χ=-22k exp(-2t) ≠ 0` for any nonzero k.
This is a **literal off-shell counterexample** to assuming that the
supplementary free-field EOM automatically follows from an arbitrary
radius background. It does NOT claim to exhaust all solutions of the
coupled full Einstein/scalar equations or prove universal impossibility
of a 27D interacting-scalar theory. The reduction changes field content
and requires a source-justified K27 action on χ and all other fields.

**Executed exact finite receipt:** new script
`scripts/check_27d_scalar_repair_consistency.py` (510 rational
(d,a) coefficient examples; d26 k²32, d10 k²0, d<10 negative slope
square; flat-base χ EOM counterexample; natural versus rescaled B
form). Equivalent local source run PASS; the committed branch file was
not byte-replayed, so DO NOT claim an exact Git-blob execution.

**Cross-prover Lean #84:** its existing
`Integration/DASHITOE/BosonicM27CoefficientCut.lean` now source-writes
`supplementalScalarSlopeSquared`,
`scalarRepairFormalCoefficient`, `scalarSlopeSquaredAtTwentySix`,
`scalarSlopeSquaredAtTen` and
`freeScalarOffShellResidualNonzero`, as algebraic consumers of the
original correct d−10 gap. Lean kernel/lake still UNVERIFIED.

### K27 source-owner obstruction is MORE specific than the 125/121 ratio

Keith Glennon, *Bosonic M-Theory From a Kac-Moody Algebra Perspective*
(2025), https://arxiv.org/abs/2501.03000, §§VII–VIII:
- Source: `K27=D24+++` in 26D has physical **2-form Kalb–Ramond**
  and a **22-form dual Kalb–Ramond potential**, along with the
  corresponding dual dilaton/graviton generators in its level
  decomposition.
- The natural candidate `E27` level-one 27D *three-form* requires a
  **22-form dual potential** for `F4`, since `27-3-2=22`;
  26D B2 likewise requires `26-2-2=22`. The **equal index rank
  does not imply the needed generator is present or is the same
  representation**.
- Glennon's proposed `K27→E27` generator correspondence requires
  `[R^{c1c2}, R_{d1..d22}]=0`, but his candidate E27 image is
  argued to have a nonvanishing higher-level commutator. He explicitly
  states the full level-eight E27 algebra was not computationally
  available to verify this specific relation directly (§VII).
  Treat “K27 is not a subalgebra of E27” as a *source argument
  within a proposed correspondence*, not an Agda/Lean kernel theorem.
- §VIII independently argues the prescribed E27 decomposition lacks
  the correct purely antisymmetric 22-form dual generator and the
  appropriate dual-graviton rank, so its standard first-order duality
  equations cannot be inhabited in the stated field content.
  A freely added scalar correcting one kinetic number does not pay
  these dual-generator and coset obligations.

**The better physical Pareto:** pursue the ALREADY ESTABLISHED
`K27` **26D closed-bosonic-string effective theory** on its source
space, and attach any 27D alternative only if an explicitly new,
representation-preserving field extension is supplied. Do not invent
another speculative 27D action or a new `E27` computation from a
cardinal match with the 27-site spatial hypervoxel.

### Lean #52 prior art: genuine 27-dimensional ALBERT PRODUCT, not just 27 sites

The open [Lean Albert PR #52](https://github.com/chboishabba/dashi_lean4/pull/52),
inspected head `9478679475bd7bb91af287cedb580470296433f1`,
contains `scripts/check_griess1990_albert_f3cubed_homogeneous_product.py`
and actual native rational Albert product/trace and S3
Hamiltonian theorems. It implements and attributes R. L. Griess Jr.
(1990), DOI 10.1016/0021-8693(90)90176-O, with
`e_x ∘ e_y = (-2)^(-c(x,y)) ω^(g(x,y)) e_(x+y)`,
for x,y in the abstract CHARACTER group `F3³`.

For unit `e_0`, every nonzero `a` (26 choices) satisfies
`e_a ∘ e_0=e_a`, `e_a ∘ e_(-a)=e_0`,
`e_a∘e_a=e_(-a)`. This proves that the 26-dimensional non-unit
homogeneous grade SPAN is **not a Jordan ideal/subalgebra**:
its product leaks into the unit. It is a genuine **operation-level
source comparison** with our separately proven original path
`L δ_origin=6δ_origin−∑neighbours`, where the 26 non-origin
SITE span also leaks into the distinguished origin.

**But the two leakages are different operators.** The Griess
homogeneous 27 is a complex `Q(ω)`-based exceptional Jordan
algebra; the Cube27 is a real finite graph with 54 open path edges;
`F3³` addition gives periodic C3³ with 81 edges. The Albert
left-multiplication by non-unit elements generally breaks full F4
symmetry; **it is NOT claimed F4 equivariant**, consistent with the
existing conditional Schur/spectral no-go for *unchanged graph L*
as full irreducible F4 intertwiner. No physical 26D Lorentzian,
bosonic worldsheet, Monster VOA or Jordan-to-path Hamiltonian
intertwiner is manufactured by comparing these source formulas.

The new Agda test
`scripts/check_27_origin_albert_griess_product_cut.py`
reuses the EXACT previously sourced multiplication formula and
checks all 26 nonzero/opposite products and 13 pairs with exact
rational/Eisenstein coefficient arithmetic. Equivalent local test
PASS. Lean #52 remains the canonical algebra owner; **do not
duplicate its complete Jordan identity/classification machinery**.

### Revised phase statuses (supersede ambiguous “alternative action” requests)

- **A3**: original simple gravity+three-form *fails* 125/121.
- **A3b**: additional free scalar *formally repairs coefficient*
  at k²=32a² but independently fails automatic free EOM
  on an explicit off-shell background; new source field dynamics
  and K27 invariance UNPAID.
- **A4**: source-level E27/K27 dual-generator, commutator and
  coset mismatch is a stronger independent boundary. Its full
  level-eight commutator was not provided as an explicit source
  computation; do not pretend to have proved one.
- **A5**: actual Griess/Albert 27→1+26 Jordan operation known on
  Lean #52, showing source-real unit mixing. Same-object
  Jordan↔Cube27↔physical string *operator/inner product*
  intertwiner still open.
- **A6**: preferred consumer 26D `K27` direct string
  effective theory, existing worldsheet/Monster/BRST owners,
  and canonical YM/NS source analytic problems separately.
