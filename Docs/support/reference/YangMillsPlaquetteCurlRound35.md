# Yang–Mills Round 35 — literal plaquette differentiation, covariant curl and adversarial stress test

## Status

Round 35 advances the proof-bearing Gate-I producers. It does not add another endpoint record and does not claim to close the selected-background Wilson estimate.

The new checked targets are:

1. the literal first derivative of the same four physical link jets used by the sixteen-atom Hessian;
2. its exact right-trivialized covariant-curl form;
3. factorization of the covariant-minus-flat curl through explicit adjoint link defects;
4. selected-background/same-perturbation instantiation;
5. a canonical four-singleton/eleven-higher-order partition for every named Wilson atom defect;
6. exact assembly of that partition into the computed plaquette Wilson defect;
7. an exact rational adversarial test showing why the Euler–Lagrange correlation remains necessary;
8. a fail-closed audit of the newly surfaced Einstein–Cartan–Yang–Mills monograph and its later regulated-slab paper.

A static audit is not a kernel result. Kernel acceptance is claimed only after the focused Agda workflow succeeds.

## 1. Literal first variation

For the repository's ordered plaquette

```text
P = A B C^-1 D^-1
```

and the right-exponential physical perturbation convention, Round 35 proves that the generated first derivative is the sum of exactly four ordered terms:

```text
P' = A' B C^-1 D^-1
   + A B' C^-1 D^-1
   + A B (C^-1)' D^-1
   + A B C^-1 (D^-1)'.
```

The third and fourth first jets are not inserted by an independent sign convention. They unfold from the existing physical inverse-link jets:

```text
(C exp(t X2))^-1|'0 = -X2 C^-1,
(D exp(t X3))^-1|'0 = -X3 D^-1.
```

The finite list of first-variation atoms has length four and sums exactly to the recursively differentiated ordered product.

Formal owner:

```text
DASHI/Physics/YangMills/
  BalabanP33PhysicalPlaquetteFirstVariationExact.agda
```

## 2. Exact right-trivialized covariant curl

Let

```text
A = U0,
B = U1,
C = positive link underlying the third inverse factor,
D = positive link underlying the fourth inverse factor.
```

Round 35 proves first, for arbitrary rational quaternions, a norm-weighted polynomial identity. For unit links the norm weights become one, yielding

```text
P' P^-1
  = Ad_A X0
  + Ad_(A B) X1
  - Ad_(A B) X2
  - Ad_(A B C^-1) X3.
```

The repeated `Ad_(A B)` is essential. It follows from the literal derivative

```text
(C exp(t X2))^-1|'0 = -X2 C^-1,
```

so the third insertion is transported by the prefix before the inverse factor. This transport order is derived from exact quaternion multiplication rather than guessed from a continuum mnemonic.

The reverse ordered product is also proved to be the right inverse of the physical plaquette product using the four unit-norm link equalities.

Formal owner:

```text
DASHI/Physics/YangMills/
  BalabanP33PhysicalCovariantPlaquetteCurlExact.agda
```

Primary references recorded in the Agda header:

- Brian C. Hall, *Lie Groups, Lie Algebras, and Representations: An Elementary Introduction*, DOI `10.1007/978-3-319-13467-3`;
- Kenneth G. Wilson, *Confinement of Quarks*, DOI `10.1103/PhysRevD.10.2445`;
- Tadeusz Bałaban, *Propagators for Lattice Gauge Theories in a Background Field*, DOI `10.1007/BF01240355`.

## 3. Flat-curl baseline

For four flat right-exponential jets, the ordered first derivative is exactly the pure quaternion associated to the oriented discrete curl:

```text
P'_flat
  = pure(X0 + X1 - X2 - X3).
```

Its quaternion scalar part is therefore exactly zero. This is the first-derivative companion to the existing theorem that the flat Wilson second variation is the squared curl norm.

The same identity is instantiated on the literal physical identity background.

Formal owner:

```text
DASHI/Physics/YangMills/
  BalabanP33FlatPlaquetteFirstVariationCurlExact.agda
```

## 4. Covariant-minus-flat defect factorization

Define

```text
curl_A = Ad_A X0 + Ad_AB X1 - Ad_AB X2 - Ad_ABC^-1 X3,
curl_1 = X0 + X1 - X2 - X3.
```

Round 35 proves the exact decomposition

```text
curl_A - curl_1
  = (Ad_A X0 - X0)
  + (Ad_AB X1 - X1)
  - (Ad_AB X2 - X2)
  - (Ad_ABC^-1 X3 - X3).
```

Every adjoint defect is then replaced by the checked quaternion factorization

```text
Ad_U X - X
  = (U - 1) X U^-1 + X (U^-1 - 1).
```

This exposes the shared prefixes `A`, `AB`, and `ABC^-1`. A sharp selected-background proof must exploit correlations among these terms rather than estimate four unrelated links independently.

Formal owner:

```text
DASHI/Physics/YangMills/
  BalabanP33CovariantCurlDefectFactorizationExact.agda
```

## 5. Same selected background and same perturbation

The first-variation/covariant-curl theorem and the defect factorization are transported onto the exact selected variational background already used by the Round-34 physical-radius and terminal-Hessian composition.

For every selected perturbation family, the following objects now share one background and one perturbation field:

```text
selected variational background,
physical first variation,
physical covariant curl,
adjoint-defect factorization,
gauge residual,
constraint residual,
terminal Hessian.
```

Formal owner:

```text
DASHI/Physics/YangMills/
  BalabanSelectedBackgroundCovariantCurlInstantiationExact.agda
```

## 6. Canonical sixteen-atom linear/nonlinear partition

For one named Wilson placement, write its four selected background factors as

```text
Ai = Bi + Di,
```

where `Bi` is the corresponding identity-background selected factor and `Di` is its exact quaternion difference.

Exact ordered multiplication proves

```text
A0 A1 A2 A3 - B0 B1 B2 B3
  = linear4(D;B) + nonlinear11(D;B).
```

The first term is the sum over singleton defect subsets:

```text
D0 B1 B2 B3
+ B0 D1 B2 B3
+ B0 B1 D2 B3
+ B0 B1 B2 D3.
```

The second term contains all eleven ordered products with at least two defect factors: six pair terms, four triple terms and the quartic term. Therefore every named placement has exactly four singleton terms and eleven higher-order terms.

This expansion is proved componentwise over exact rational quaternions. It does not commute factors and does not appeal to an abstract multilinearity receipt.

The expansion is then instantiated on each of the four diagonal and twelve ordered-cross placements. Summing the sixteen exact scalar identities proves

```text
D2W_A(p)[h,h] - D2W_1(p)[h,h]
  = canonicalLinearPart_p(A,h)
  + canonicalGroupedNonlinearRemainder_p(A,h).
```

Round 34 previously accepted functions called `physicalLinearPart`, `physicalGroupedRemainder` and an equality connecting them. Round 35 now constructs those functions and the equality from the literal named atoms. Callers may supply only the two signed lower bounds:

```text
-(rho/36) C_p(h) <= canonicalLinearPart_p(A,h),
-(rho/144) q_p(h) <= canonicalGroupedNonlinearRemainder_p(A,h).
```

Those canonical bounds construct the existing physical W-local object and compose directly to the terminal coefficients

```text
10739/196608,
1/32.
```

Formal owner:

```text
DASHI/Physics/YangMills/
  BalabanP33PhysicalWilsonLinearNonlinearPartitionExact.agda
```

## 7. Exact adversarial radius stress test

Before attempting the `rho/36` selected-curvature estimate, Round 35 checks a rational unit-quaternion adversary.

Set

```text
rho = 1/8192,
q = (67108863/67108865,
     16384/67108865,
     0,
     0).
```

The module proves exactly:

```text
N(q) = 1,
N(q^-1 - 1) = 4/67108865,
N(q^-1 - 1) + 1/1125899923619840 = 4 rho^2.
```

Thus `q` lies strictly inside the configured radius.

Choose two insertions which cancel at the flat background:

```text
X0 = Y,
X1 = -Y,
X2 = X3 = 0.
```

Then

```text
curl_flat = 0,
```

but transporting the second insertion by `q` gives

```text
N(curl_q)
  = 1073741824/4503599761588225.
```

For the local cross-charge value `C = 6`, the nominal linear scale is

```text
(rho/36) C = 1/49152.
```

The squared target scale has the exact positive deficit

```text
N(curl_q) - (1/49152)^2
  = 2589569785603817471
    /10880332700790838158950400
  > 0.
```

This is not a counterexample to the desired selected-background theorem: the adversary is not asserted to satisfy Bałaban's Euler–Lagrange equation. It is a fail-closed regression proving that radius and flat cancellation alone still do not supply the correlated curvature estimate.

Formal owner:

```text
DASHI/Physics/YangMills/
  BalabanP33CovariantCurlRadiusStressTestExact.agda
```

## 8. Einstein–Cartan–Yang–Mills and regulated-slab claim audit

The attached material also surfaced work by Emmanouil Karolos Čižek. Round 35 records three cited sources rather than treating their conclusions as imported theorems:

- *A Constructive Einstein–Cartan–Yang–Mills Theory with Positive Mass Gap in Four Dimensions*, DOI `10.5281/zenodo.17246443`;
- *A Structural and Conceptual Overview of A Constructive Einstein–Cartan–Yang–Mills Theory with Positive Mass Gap in Four Dimensions*, DOI `10.5281/zenodo.17718647`;
- *Mixing of Boundary Langevin Dynamics for Regulated Four-Dimensional Yang–Mills Slabs*, DOI `10.5281/zenodo.18280110`.

The audit introduces distinct signatures for:

```text
Einstein-Cartan-Yang-Mills theory,
pure four-dimensional Yang-Mills,
auxiliary boundary Langevin generator,
boundary slab transfer kernel,
reconstructed physical Hamiltonian.
```

It proves that none of the following promotions is definitional:

```text
Einstein-Cartan-Yang-Mills = pure Yang-Mills,
auxiliary boundary Langevin generator = slab transfer kernel,
slab transfer kernel = reconstructed physical Hamiltonian.
```

For the monograph, the first open theory bridge is:

```text
torsionGravitySectorExactlyDecouplesToPureYM.
```

For the narrower slab route, the first open continuation is:

```text
ultravioletContinuumOnR4ActuallyConstructed.
```

The slab result remains represented as a conditional theorem about a regulated/fixed-spacing construction, not as the Clay Hamiltonian mass gap.

Formal owner:

```text
DASHI/Physics/YangMills/
  YangMillsCizekEinsteinCartanClaimAuditExact.agda
```

## 9. Exact remaining Gate-I frontier

Round 35 closes:

```text
selectedBackgroundPlaquetteFirstVariation
selectedBackgroundCovariantDiscreteCurlIdentity
sixteenAtomsPartitionIntoLinearAndNonlinear
canonicalPhysicalWilsonDecomposition
```

The remaining proof-bearing sequence is now:

```text
variationalEulerLagrangeEquationAtSelectedBackground
selectedBackgroundRegularityControlsPlaquetteCurvature
selectedBackgroundCurvatureLinearLower
canonicalWilsonLinearPartIsCurvatureExpression
groupedSixteenAtomNonlinearRemainderLower
selectedBackgroundPhysicalWLocal
selectedBackgroundHessianOneThirtySecond
```

The two numerical targets remain:

```text
-(rho/36) C_p(h) <= canonicalLinearPart_p(A,h),
-(rho/144) q_p(h) <= canonicalGroupedNonlinearRemainder_p(A,h).
```

The first inequality must use the constrained selected-background equation or an equivalent correlated curvature theorem. The exact stress test rules out replacing it by a radius-only estimate.

The second inequality must preserve the canonical grouped atom structure; an indiscriminate triangle inequality may spend more than the available `rho/144` budget.

## 10. After Gate I

Once those two estimates are proved, the existing Round-34/Round-35 composition yields

```text
H_A[h,h] >= 10739/196608 ||h||^2
           >= 1/32 ||h||^2.
```

The next highest-alpha work is then:

```text
literal Hessian matrix representation,
Hermiticity,
finite stencil,
row/column interaction mass,
constructive inverse,
physical Combes–Thomas decay,
one scale-uniform RG step.
```

No finite-volume theorem, including the completed Gate-I theorem, is definitionally equal to the Clay conclusion. The Round-32 Clay contract and Round-33 source/all-group guards remain authoritative.
