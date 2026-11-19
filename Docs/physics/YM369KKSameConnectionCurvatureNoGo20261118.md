# P3/P7 369 Yang–Mills / KK same-connection maximum cut — 2026-11-18

## Executive mathematical result

**NEGATIVE for the literal full-field identity:** the classical charge-one BPST
SU(2) instanton connection on flat spatial R4 cannot be related by an SU(2)
gauge transformation to the Cartan embedding of the single-centre Gross–Perry–
Sorkin KK U(1) monopole connection. This statement is specifically about
identifying these connections as the same gauge field, not about solutions of
coupled Einstein–Yang–Mills or gravitational spin-connection constructions.

**POSITIVE restricted bridge:** the EXISTING repository's
`DASHI/Physics/Electromagnetism/U1SU2GroupTorusExact.agda` constructs a
literal U(1) group and a group homomorphism to the existing SU(2)
unit-quaternion carrier. The new `YM369KKU1SameConnectionBoundaryExact.agda`
proves commutativity of the original U(1), reuses that actual inclusion and
the actual source CMP109 spatial C3, and exhibits finite quaternion
noncommutativity. It does not build a physical KK bundle isomorphism.

## 1. Same-object obstruction (not just a symmetry comparison)

Use `su(2)` represented by imaginary quaternions with classical
`[e_a,e_b]=2 epsilon_{abc}e_c`, as in the existing DASHI
`BalabanSU2LieBracket`. A KK magnetic circle connection `a` lies in
`u(1)`. Its fixed SU(2) Cartan embedding `a e3` has
`F=(da)e3`, and all two-form curvature values commute:
`[F_ij,F_kl]=0`.

For the standard charge-one BPST instanton in regular gauge on Euclidean
R4, using self-dual 't Hooft symbols and `rho>0`,
`F^a_ij(x)=-4 rho² eta^a_ij / (|x|²+rho²)²`. At `x=0` choose
`eta^3_12=1`, `eta^2_13=-1`. Then

```
F12 = -4 e3/rho²
F13 = +4 e2/rho²
[F12,F13] = +32 e1/rho^4
||[F12,F13]||² = 1024/rho^8 > 0
```

Conjugating both curvatures by ANY SU(2) gauge transformation conjugates
their commutator, preserving nonzero status (and norm under the adjoint
invariant metric). Therefore no such gauge transformation maps this entire
BPST connection to the embedded KK U(1) connection. Even an abstract
identical C3 coordinate permutation in the two systems cannot evade
this invariant.

`scripts/check_kk_ym369_same_connection_obstruction.py` tests the above
exactly using SymPy and checks C3 bracket covariance and Chern -1 with
`a=1/2(dchi+cos(theta)dphi)`, `chi` period `4pi`.
**In-session source-equivalent local script execution PASS**, 5 reported
checks, 2026-11-18. Original committed blob has not been run through a
repository checkout and the Agda source is not kernel-certified.

## 2. What the 369/YM code actually contributes

| Native code owner | Concrete role | Guardrail |
|---|---|---|
| `BalabanSU2QuaternionCarrier` | literal group multiplication, norm, conjugation | algebra over canonical real authority, not a smooth metric |
| `BalabanSU2LieBracket` | 3-component quaternion commutator `2 cross` | needed for nonabelian curvature |
| `SU2Bracket369OrientationBridgeExact` | source bracket ↔ oriented three-axis 369 skeleton | orientation structure does not define a physical soliton |
| `BalabanCMP109SpatialC3ActionExact` | actual source x/y/z cyclic rotation with time fixed | source generated grid rather than KK nut |
| `BalabanC3MonsterEquivarianceAuditExact` | classical stress/C3 and literal side-four source field/curl; explicit nonlinear recovery gaps | source itself says full nonlinear same-object Q1 is open |
| `YMClayNativeSixPlaneC3SourceReductionExact` | signed six-plane native SU2 Wilson source C3 conditional on two orientation reversals | finite original Wilson source, not continuum |
| `CompactLieLatticeGauge` | arbitrary edge-group holonomy and gauge covariance | exact lattice paths, not global smooth parallel transport |
| `U1SU2GroupTorusExact` | real U1 group inside actual unit quaternion SU2 | subgroup only, not gauge connection equivalence |
| `HopfQuaternionAxisProjectionExact` | real quaternion SU2/U1 phase invariant Hopf axis | S2 atlas/connection/Chern original physical identification remains a gate |
| `KKYM369SingleCentreMonopoleSpinConfigurationMaxCut20261118.md` | classical 5D KK mono and BPST solution comparison | two distinct parent actions |

**This is a targeted deep audit, NOT an exhaustive search of every historical
369/YM PR or every Clay Yang–Mills round.** Search index, branch coverage,
and cross-PR exact-head review still matter. Especially distinguish the
CMP109 physical generated-action recovery compiler, the original four-axis
lattice/YM continuum Clay lanes, and the finite C3 source.

## 3. Can we still relate them in one parent action?

Three legitimate, clearly different programme choices:

1. **Cartan reduction of SU2**: choose gauge fields of the form `A=a T3`;
   this gives a valid embedded abelian sector, but loses the noncommuting
   BPST curvature and generally its instanton topological charge. A nontrivial
   U1 bundle needs transitions; gauge choice alone is not a global trivialisation.
2. **5D coupled Einstein–SU2 Yang–Mills**: choose
   `S= ∫sqrt(-G)[R/(16pi G5) - (1/4g5²) F^a_AB F^{aAB}]`.
   For a nonzero BPST energy, flat spacetime is not a solution to the
   coupled Einstein equation; backreaction, boundary conditions, spatial
   compactification and full 5D constraints must be solved. The KK circle
   connection remains geometric and the YM SU2 connection remains independent
   unless a *new* explicit identification is proved.
3. **Geometric induced SU2 spin connection**: use the SO(4) spatial
   Levi-Civita connection of Taub–NUT and project into one SU2 spin factor.
   This genuinely derives a nonabelian gauge connection from a single
   metric, but it is NOT the KK off-diagonal circle U1 connection and need
   not equal BPST. Derive its curvature, instanton number and YM equations
   before asserting equivalence. This is the preferred next constructive
   same-parent-geometry path.

## 4. Recent fast π work: useful numerically, not the missing physics

A distinct recent user-referenced source is
`research/constructive-pi-binary-split-20261118`; GitHub commit
`62c0940` records merging that branch into master on 2026-11-18.
Existing source documents:
- `Docs/roadmaps/ConstructivePiBinarySplitMaxCut20261118.md`;
- `Docs/roadmaps/ConstructivePiRadixTwoC3NegativeControl20261118.md`;
- `Docs/roadmaps/ConstructivePiEulerReuseNegativeControls20261118.md`;
- `scripts/check_bishop_fast_pi_binary_split.py`;
- `scripts/check_bishop_fast_pi_power_two_split.py`.

The roadmap reports Machin binary split ≈63.829 ms for 10k-digit
enclosure evaluation in its stated historical benchmark, and the later
power-of-two comparison gives a distinct ≈35.584 ms 10k-digit finite-sum
benchmark. These are DIFFERENT workloads: do not equate their timings.
The attempted 1/8+3/41 decomposition was slower than original Machin.
In particular, no genuine C3 cubic modular equation, Chudnovsky
same-Bishop-real proof, or Agda `--safe` acceptance follows from these
Python benchmarks.

Relevance to present work: exact integer rational arithmetic and eventual
certified π enclosures can support numerical values of 4πm fibre period,
Chern 1/(2π) normalization and 8π²/g5² instanton energy.
**The finite noncommutator obstruction does not need numerical π at all.**
π computation does not establish U1↔SU2 same-object field identity,
self-duality, smooth bundle topology, nor nonlinear stability.

## 5. Revised exact acceptance order

- [x] U1↪SU2 original group-level morphism, reusing original owner.
- [x] Exact U1 commutativity proof from its literal coordinate multiplication,
  **source-written kernel pending**.
- [x] Exact Q8 noncommuting witness and native source XYZ spatial C3,
  **source-written kernel pending**.
- [x] Exact symbolic BPST curvature noncommutator and KK Cartan zero
  commutator: local SymPy PASS, mathematical no-go for literal identity.
- [ ] Pin one selected curved 5D parent-action solution with an ACTUAL
  nonzero SU2 stress tensor satisfying Einstein equations.
- [ ] Or derive Taub–NUT Levi-Civita SU2 spin connection from the SAME
  metric, verify curvature, Yang–Mills field equations, global patches,
  holonomy and topological number.
- [ ] Map smooth curvature through the SAME source-defined physical
  369/YM continuum field, not a mere finite C3 analogy.
- [ ] Derive physical soliton configuration space, 2π rotation/exchange
  paths, FR quantization and nonlinear stability.
- [ ] Reconcile π numeric backend and exact Bishop real normalization
  only where a proof requires certified analytic constants.

## 6. Attribution and nonpromotion

- **Classical primary authors**: Belavin–Polyakov–Schwartz–Tyupkin
  (1975), BPST instanton; Gibbons–Hawking (1978), gravitational
  multi-instantons; Gross–Perry (1983) and Sorkin (1983), KK monopole;
  Cartan and Lie-group structure, quaternionic SU2, standard Chern-Weil
  and gauge adjoint covariance.
- **Existing project code/owner**: the exact literal DASHI module owners
  in §2, plus fast-π branch and documents in §4. Cite unchanged.
- **User-originated research problem**: assess whether native 369 YM
  makes KK/Hopf configurations one physical field; inspect recent fast π.
- **New bounded analysis/implementation**: comparison of field curvature
  brackets on ORIGINAL algebra conventions, exact no-go script, explicit
  U1 Cartan/finite quaternion Agda boundary, source-ledger clarification.
  ChatGPT-assisted 2026-11-18.
- **Trust boundary**: no new antigravity, spin-1/2 particle, continuum
  Yang–Mills mass gap, stable coupled KK-YM soliton, or full bridge is
  claimed. No full repo historical audit or local Agda kernel acceptance.
