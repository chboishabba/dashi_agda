# Frontier productive completion — round two

This extension hardens and generalises the first frontier tranche. It imports the first cumulative root, then adds only corrected proof-bearing modules.

## Hodge direct-sum uniqueness

`RationalThreeWayHodgeCoordinateUniquenessExact.agda` normalises rational zero additions explicitly and proves that two decompositions

```text
x = exact(e) + harmonic(h) + coexact(c)
  = exact(e') + harmonic(h') + coexact(c')
```

imply

```text
e=e', h=h', c=c'.
```

The canonical projection coordinates therefore form a genuine finite direct-sum certificate.

## Projective-space Hodge pattern

`ProjectiveSpaceHodgeBasisExact.agda` represents the hyperplane powers

```text
1,H,...,H^n
```

by `Fin(n+1)`. Every basis class has bidegree `(k,k)`. The file checks:

```text
P2: (b0,b1,b2,b3,b4)=(1,0,1,0,1),
P3: (1,0,1,0,1,0,1).
```

Geometric construction, de Rham comparison and hard Lefschetz remain separate.

## Generic finite Cook–Levin layer

`GenericFiniteRunTableauExact.agda` proves for every finite nondeterministic run:

```text
n transition steps <=> n+1 tableau rows,
number of local transition constraints = n.
```

Run certificates convert to tableaus and back. Bounded accepting runs convert to accepting tableaus and back with the same step bound. Boolean cells, CNF conversion and polynomial bit-size are still explicit obligations.

## Generic differential-vertex construction

`FiniteDifferentialVertexAlgebraExact.agda` proves generically that a commutative unital algebra with square-zero derivation `D` supports the finite modes

```text
a_(-1)b=ab,
a_(-2)b=(Da)b,
a_n b=0 otherwise.
```

Vacuum, creation, translation, truncation and exact commutation of the truncated fields are derived solely from the algebra laws.

`SquareZeroDifferentialVertexAlgebraBridgeExact.agda` instantiates the theorem with

```text
A=Q+Qx+Qy,
(Qx+Qy)^2=0,
D(x)=y,
D(y)=0,
```

and proves the generic and coordinate constructions agree.

## Finite Heisenberg/Fock window

`RankOneHeisenbergFockWindowExact.agda` acts on rational polynomials through degree four:

```text
X = multiplication by x followed by truncation,
D = formal differentiation.
```

For every polynomial of degree at most three it proves

```text
D X - X D = 1.
```

The number operator `XD` has eigenvalues `0,1,2,3` on the first four monomials. Infinite modes, normal ordering and the complete Heisenberg VOA remain separate.

## Finite OS2

`FiniteReflectionPositivityExact.agda` uses a diagonal two-state reflected kernel. For every half-observable `F`, its OS quadratic form is exactly

```text
F(+)^2+F(-)^2.
```

Reflection positivity is therefore carried by an explicit sum-of-two-squares witness.

## Finite OS4

`FiniteProductClusteringDenominatorClearedExact.agda` proves the denominator-cleared product-measure identity

```text
4 E[FG] = (2E[F])(2E[G]).
```

Thus the connected correlation is exactly zero at every declared separation.

## Finite KP budget

`FinitePolymerKPBudgetExact.agda` uses three polymers. Alpha is incompatible with beta and gamma, while beta and gamma are compatible. Unit weighted activities give incompatibility sums

```text
alpha:2,
beta:1,
gamma:1,
```

matching the selected budgets. The five compatible families are enumerated and the hard-core partition function is `5`.

## Finite constructive Yang–Mills ladder

`YangMillsFiniteConstructiveLadderExact.agda` packages:

```text
finite OS2 sum-of-squares,
finite exact clustering,
finite KP budget,
volume-indexed spectral gap 3.
```

Model tags prove that this independent finite system is neither the interacting nonabelian lattice Yang–Mills measure nor the continuum theory. It therefore informs the OS2/OS4/KP proof architecture without promoting a toy model to the Clay theorem.

## Validation

Run:

```bash
AGDA_JOBS=1 bash scripts/check_frontier_hodge_automorphic_spectral_round2.sh
```

The aggregate target is:

```text
DASHI.EverythingFrontierHodgeAutomorphicSpectralRound2
```

The checker first validates the complete first frontier layer, then scans and type-checks only the hardened round-two authority surface.
