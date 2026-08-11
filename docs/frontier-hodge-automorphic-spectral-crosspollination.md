# Frontier Hodge, automorphic and spectral cross-pollination

This tranche converts the priority programme after PR #449 into proof-bearing finite mathematics. It is stacked on `agent/millennium-crosspollination-rh-hodge-bsd-pnp-poincare-voa` and preserves every global open-problem boundary.

## 1. Cochains and finite Hodge theory

`FiniteCochainComplexExact.agda` introduces a three-term complex

```text
C0 --d0--> C1 --d1--> C2,
d1 d0 = 0.
```

It proves:

```text
exact one-cochain => closed one-cochain,
cochain maps preserve closed cochains,
cochain maps preserve exact cochains,
cochain maps compose,
one-cochain homotopies give cohomologous images,
product complexes preserve componentwise closed/exact witnesses.
```

No quotient is silently identified with cohomology.

`FiniteHodgeEnergyExact.agda` defines

```text
Delta = d0 d0* + d1* d1
```

and proves

```text
<Delta x,x> = <d0* x,d0* x> + <d1 x,d1 x>.
```

Under the supplied positive-definiteness implication,

```text
Delta x = 0 => d0* x = 0 and d1 x = 0.
```

`RationalThreeWayHodgeDecompositionExact.agda` constructs the inhabited model

```text
Q^3 = exact axis + harmonic axis + coexact axis.
```

The three projections are idempotent, pairwise annihilating and orthogonal, sum to the identity, and are unique. Its Laplacian has mode values `1,0,1`, and its kernel is exactly the harmonic axis.

`ProjectiveLineProductHodgeExact.agda` computes the tensor-product Hodge basis of `P1 x P1`:

```text
h00=1, h11=2, h22=1,
(b0,b1,b2,b3,b4)=(1,0,2,0,1).
```

## 2. Finite Dirichlet and Euler-product algebra

`FiniteEulerProductExact.agda` proves in an arbitrary commutative semiring:

```text
sum over all finite choices of local factors
=
product of the finite local sums.
```

This is the finite Cartesian expansion underlying Euler products. It does not use convergence.

`FiniteMultiplicativeDirichletExact.agda` represents formal prime-power factorisations and proves:

```text
coefficient(left ++ right)
  = coefficient(left) coefficient(right),
weight(left ++ right)
  = weight(left) weight(right),
monomial(left ++ right)
  = monomial(left) monomial(right).
```

For disjoint prime support this is the finite algebraic form of

```text
a_mn=a_m a_n,
(mn)^(-s)=m^(-s)n^(-s).
```

`TruncatedLFunctionExact.agda` defines

```text
P_p(T)=1-a_p T+pT^2
```

and finite products of these local factors. Pointwise agreement of elliptic Frobenius coefficients and modular Fourier coefficients proves equality of all local factors and every selected truncated product.

`MellinSplitFunctionalEquationExact.agda` proves the algebraic heart of the Mellin functional equation. If lower and upper transform pieces satisfy

```text
lower(s)=epsilon upper(k-s),
upper(s)=epsilon lower(k-s),
```

then

```text
Lambda(s)=epsilon Lambda(k-s).
```

A rational reflection-symmetric example inhabits the theorem. Integral convergence, Gamma completion and modular change of variables remain separate.

## 3. BSD local arithmetic

For

```text
E: y^2=x^3-x,
```

`EllipticCurveSmallPrimeFrobeniusExact.agda` adds the checked rows:

| p | #E(F_p) | a_p |
|---:|---:|---:|
| 3 | 4 | 0 |
| 5 | 8 | -2 |
| 7 | 8 | 0 |
| 11 | 12 | 0 |
| 13 | 8 | 6 |
| 17 | 16 | 2 |
| 19 | 20 | 0 |

Every row includes its full affine fibre-count vector and a proof of

```text
|a_p|^2 <= 4p.
```

The `p=5` row reuses the literal 25-pair enumeration from PR #449.

`SmallPrimeTruncatedEulerProductExact.agda` constructs

```text
product_{p in {3,5,7,11,13,17,19}} (1-a_p T+pT^2)
```

and proves it equals the product associated to any selected modular coefficient candidate agreeing on all seven traces.

`EllipticCurveTwoTorsionAndBadPrimeExact.agda` checks the rational affine points

```text
(0,0), (1,0), (-1,0)
```

and constructs their two-torsion table with the point at infinity as `C2 x C2`. Associativity, commutativity and exponent two are proved by exact xor laws. It also proves

```text
64=2^6
```

and separates all seven selected odd primes from the bad-prime support candidate `2`.

The geometric chord-and-tangent identification, minimal model, conductor exponent, full torsion classification, rank, descent, Selmer and Sha computations remain explicit boundaries.

## 4. Complexity

`PSubsetNPTrivialCertificateExact.agda` proves `P subset NP` in the repository's own cost model. A deterministic decider becomes an NP verifier with the unique unit certificate. The only assumptions are explicit polynomial closure for ignoring the certificate and for the unit certificate size.

`MachineRunCertificateExact.agda` proves an exact equivalence between:

```text
n-step nondeterministic reachability
```

and

```text
a finite successor path of length n with local transition witnesses.
```

Bounded acceptance therefore produces a finite accepting certificate with the same step-bound proof, and the certificate reconstructs the accepting run.

`FiniteCookLevinTableauExact.agda` constructs a nonempty finite Cook--Levin seed:

```text
start -> work -> accept.
```

Its three-row tableau has separate initial, transition and acceptance constraints. A satisfying tableau yields the exact accepting run, and the canonical run yields the satisfying tableau. Generic tape encoding, window clauses, CNF generation and polynomial size remain separate.

## 5. Vertex algebra and Fock grading

`SquareZeroDifferentialVertexAlgebraExact.agda` uses the commutative algebra

```text
A = Q + Q x + Q y,
(Q x + Q y)^2 = 0,
D(x)=y,
D(y)=0.
```

Thus

```text
D(a+b x+c y)=b y.
```

The file proves:

```text
D is nonzero,
D^2=0,
D(uv)=D(u)v+uD(v),
u_(-1)v=uv,
u_(-2)v=(Du)v,
```

as well as vacuum, creation, translation-mode identities and exact commutation of the truncated bivariate fields. The earlier proposed dual-number model was deleted because its nonzero derivation was not square-zero in characteristic zero.

`RankOneFockPartitionGradingExact.agda` constructs oscillator bases in grades zero through five with dimensions

```text
1,1,2,3,5,7.
```

`RankOneFockEulerProductPrefixExact.agda` independently derives the same sequence from

```text
product_{n=1}^5 (1-q^n)^(-1) mod q^6.
```

The intermediate products are also checked. This gives an exact finite bridge from a Fock grading to an Euler-product character. Infinite Fock completion, Heisenberg relations, conformal structure, eta modularity and Monster `V^natural` remain distinct.

## 6. Shared spectral certification

`RationalTwoByTwoSelfAdjointSpectralExact.agda` constructs

```text
H=diag(2,5).
```

It proves self-adjointness, the exact eigenpairs, zero residuals, orthogonality, characteristic roots and spectral separation

```text
(5-2)^2=9.
```

`SharedFiniteSpectralCertificationExact.agda` defines a common enclosure certificate and adapts the existing Maaß residual-to-spectral-enclosure theorem without dropping any hypotheses.

The same file instantiates:

```text
finite Hilbert--Pólya modes 2 and 5,
finite Hodge-Laplacian modes 1,0,1,
a finite transfer-Hamiltonian gap 5-2=3.
```

The finite Hilbert--Pólya coordinates are exactly `1/2+i lambda`, hence lie on the critical line. This does not prove that they are zeta zeros or exhaust the zeta spectrum.

## 7. Yang--Mills and Maxwell

`FiniteAbelianGaugeHodgeExact.agda` uses the exact/harmonic/coexact split as a finite abelian gauge field:

```text
d0 chi=(chi,0,0),
curvature(A)=coexactCoordinate(A).
```

It proves:

```text
curvature(A+d0 chi)=curvature(A),
curvature(exact A)=0,
curvature(harmonic A)=0.
```

On the slice

```text
exactCoordinate(A)=0,
harmonicCoordinate(A)=0,
```

the Hodge Hessian is the identity, so

```text
<A,H A>=||A||^2.
```

Thus the exact finite massive sector has coercivity constant `lambda=1`.

`FiniteHodgePhysicsCrossPollinationExact.agda` connects this theorem to the existing finite gauge-adjoint and Maxwell source-current owners. It adds a finite `d^2=0` Bianchi/source-conservation consequence while preserving the existing false weighted-adjoint and full-Maxwell promotion flags.

`YangMillsHodgeCoercivityFrontierExact.agda` identifies this theorem with the existing `localFiniteCoercivity` entry stage. It keeps separate:

```text
nonabelian weighted Hodge adjointness,
finite propagator,
OS2 reflection positivity,
OS4 clustering,
KP spatial/large-field control,
volume-uniform gap,
continuum measure,
reconstructed Hamiltonian mass gap.
```

## 8. Navier--Stokes

`NavierStokesFiniteVorticityDepletionExact.agda` proves the finite inequality

```text
raw stretching
<= angle defect * kernel weight * amplitude
<= coherence bound * kernel weight * amplitude.
```

The pointwise inequality is propagated through arbitrary finite sums. A concrete two-interaction family checks totals

```text
raw=14,
controlled=20.
```

The module connects to the existing exact stretching receipt while preserving its false Clay-promotion flag. Biot--Savart construction, singular-kernel estimates, Hölder direction coherence, depleted BKM and global regularity remain separate.

## Validation

The cumulative root is:

```text
DASHI.Mathematics.CrossPollination.FrontierHodgeAutomorphicSpectralValidation
```

The whole-repository target is:

```text
DASHI.EverythingFrontierHodgeAutomorphicSpectralCrossPollination
```

Run:

```bash
AGDA_JOBS=1 bash scripts/check_frontier_hodge_automorphic_spectral_crosspollination.sh
```

The checker first runs the PR #449 checker, rejects holes, postulates, unsafe flags and trust primitives, verifies theorem/source/scope guards, and then invokes pinned Agda 2.9 on the aggregate target.
