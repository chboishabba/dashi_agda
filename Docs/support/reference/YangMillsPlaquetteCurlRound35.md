# Yang–Mills Round 35 — plaquette curl, canonical Wilson partition and budget audit

## Status

Round 35 advances the proof-bearing Gate-I lane. It does not add another endpoint record and does not claim that the selected-background Wilson estimate or the Clay problem is closed.

A static audit is not a kernel result. Kernel acceptance is claimed only after the focused Agda workflow succeeds.

The completed algebraic producers are now:

```text
selectedBackgroundPlaquetteFirstVariation
selectedBackgroundCovariantDiscreteCurlIdentity
covariantCurlDefectFactorization
sixteenAtomsPartitionIntoLinearAndNonlinear
canonicalPhysicalWilsonDecomposition
canonicalPairDeepDecomposition
squareRootFreeScaledYoungLower
genericDeepRemainderEnvelope
```

The remaining physical producers are:

```text
variationalEulerLagrangeEquationAtSelectedBackground
selectedBackgroundRegularityControlsPlaquetteCurvature
physicalSelectedFactorEnvelopeInstantiation
selectedBackgroundCorrelatedWilsonLower
groupedDeepWilsonRemainderLower
selectedBackgroundPhysicalWLocal
selectedBackgroundHessianOneThirtySecond
```

## 1. Literal first variation

For the repository’s actual ordered plaquette

```text
P = A B C^-1 D^-1
```

the generated first derivative is proved to contain exactly four ordered terms:

```text
P' = A' B C^-1 D^-1
   + A B' C^-1 D^-1
   + A B (C^-1)' D^-1
   + A B C^-1 (D^-1)'.
```

The inverse-link signs and multiplication order unfold from the existing physical jets:

```text
(C exp(t X2))^-1|'0 = -X2 C^-1,
(D exp(t X3))^-1|'0 = -X3 D^-1.
```

Formal owner:

```text
BalabanP33PhysicalPlaquetteFirstVariationExact.agda
```

## 2. Exact covariant curl

After right trivialization, exact rational quaternion multiplication gives

```text
P' P^-1
  = Ad_A X0
  + Ad_(A B) X1
  - Ad_(A B) X2
  - Ad_(A B C^-1) X3.
```

The repeated `Ad_(A B)` is essential. It is derived from the literal left derivative `-X2 C^-1`; it is not selected by analogy with a continuum formula.

The reverse ordered product is separately proved to be the physical plaquette right inverse from the four unit-link hypotheses.

Formal owner:

```text
BalabanP33PhysicalCovariantPlaquetteCurlExact.agda
```

Sources recorded in the Agda header include Brian C. Hall, *Lie Groups, Lie Algebras, and Representations*, DOI `10.1007/978-3-319-13467-3`; Kenneth G. Wilson, *Confinement of Quarks*, DOI `10.1103/PhysRevD.10.2445`; and Tadeusz Bałaban, *Propagators for Lattice Gauge Theories in a Background Field*, DOI `10.1007/BF01240355`.

## 3. Flat baseline and adjoint-defect factorization

At the identity background:

```text
P'_flat = pure(X0 + X1 - X2 - X3),
q0(P'_flat) = 0.
```

The covariant-minus-flat curl is exactly

```text
(Ad_A X0 - X0)
+ (Ad_AB X1 - X1)
- (Ad_AB X2 - X2)
- (Ad_ABC^-1 X3 - X3).
```

Every adjoint defect is factorized using

```text
Ad_U X - X
  = (U - 1) X U^-1 + X (U^-1 - 1).
```

This exposes the shared prefixes `A`, `AB` and `ABC^-1`, which a correlated selected-background estimate must exploit.

Formal owners:

```text
BalabanP33FlatPlaquetteFirstVariationCurlExact.agda
BalabanP33CovariantCurlDefectFactorizationExact.agda
BalabanSelectedBackgroundCovariantCurlInstantiationExact.agda
```

The selected-background instantiation uses the same background and perturbation already consumed by the gauge, constraint and terminal-Hessian theorems.

## 4. Canonical sixteen-atom partition

For one named Wilson placement, write its four selected factors as

```text
Ai = Bi + Di.
```

Exact ordered multiplication proves

```text
A0 A1 A2 A3 - B0 B1 B2 B3
  = sum of four singleton terms
    + sum of eleven higher-order terms.
```

The singleton terms are

```text
D0 B1 B2 B3,
B0 D1 B2 B3,
B0 B1 D2 B3,
B0 B1 B2 D3.
```

The eleven higher-order terms are exactly six quadratic terms, four cubic terms and one quartic term. No quaternion factors are commuted.

The theorem is instantiated on all four diagonal and twelve ordered-cross placements and summed to obtain the literal physical plaquette identity

```text
D2W_A(p)[h,h] - D2W_1(p)[h,h]
  = canonicalLinearPart_p(A,h)
  + canonicalGroupedNonlinearRemainder_p(A,h).
```

Thus the Round-34 decomposition is no longer caller-selected.

Formal owner:

```text
BalabanP33PhysicalWilsonLinearNonlinearPartitionExact.agda
```

## 5. The budget-compatible pair/deep refinement

The first canonical partition is algebraically natural but not numerically optimal. Put

```text
epsilon = 2 rho,
rho = 1/8192.
```

Per named placement, the six quadratic terms have coefficient

```text
6 epsilon^2,
```

while the four cubic terms and quartic term have coefficient

```text
4 epsilon^3 + epsilon^4.
```

The sixteen placement Young budgets sum to four times the local diagonal charge. Therefore the all-placement coefficients are

```text
pair  = 24 epsilon^2
      = 3/2097152,

deep  = 16 epsilon^3 + 4 epsilon^4
      = 16385/70368744177664.
```

The diagonal target is

```text
rho/144 = 1/1179648.
```

Exact arithmetic proves

```text
deep + 536723447/633318697598976 = rho/144,
```

so the cubic–quartic channel fits the diagonal budget with positive slack. In contrast,

```text
rho/144 + 11/18874368 = pair,
```

so charging all six quadratic terms to the diagonal channel is impossible at the configured constants.

The canonical decomposition is therefore refined to

```text
Wilson defect
  = correlated(singleton + pair)
  + deep(triple + quartic).
```

The pair cost per cross charge is exactly

```text
rho/256,
```

leaving the positive correlated coefficient

```text
rho/36 - rho/256 = 55/18874368.
```

Formal owners:

```text
BalabanP33PhysicalWilsonCorrelatedDeepPartitionExact.agda
BalabanP33WilsonPairDeepBudgetExact.agda
```

## 6. Square-root-free deep-remainder theorem

A new rational theorem proves that, whenever

```text
N(q) <= (s left)(s right),
s,left,right >= 0,
```

then

```text
-s(left+right)/2 <= -q0(q) <= s(left+right)/2.
```

The lower bound is obtained by applying the upper theorem to `-q`; no square root or absolute-value axiom is used.

For an ordered four-factor placement, assume

```text
N(Di) <= epsilon^2 wi,
N(Bi) = wi,
w0 w1 w2 w3 = leftCharge * rightCharge.
```

Exact norm multiplicativity then gives four cubic bounds at scale `epsilon^3` and one quartic bound at scale `epsilon^4`. Their signed scalar sum proves

```text
-(4 epsilon^3 + epsilon^4)
  * (leftCharge + rightCharge)/2
<= WilsonScalar(deepRemainder).
```

All scalar upper transports are explicit rational equalities. No unresolved factor placeholder is used.

Formal owners:

```text
BalabanP33QuaternionScaledYoungLowerExact.agda
BalabanP33WilsonDeepRemainderEnvelopeExact.agda
```

The remaining deep-channel seam is the physical selected-factor envelope instantiation: the literal positive and inverse link jets must be shown to satisfy these `Bi/Di/wi` hypotheses under the selected-background radius. Once that is supplied for all sixteen placements, the exact coefficient theorem above promotes the generic deep bound to the required physical `rho/144` lower estimate.

## 7. Exact adversarial curvature stress test

Take the rational unit quaternion

```text
q = (67108863/67108865,
     16384/67108865,
     0,
     0).
```

The repository proves

```text
N(q) = 1,
N(q^-1 - 1) = 4/67108865,
N(q^-1 - 1) + 1/1125899923619840 = 4 rho^2.
```

Thus `q` lies strictly inside the configured radius.

For

```text
X0 = Y,
X1 = -Y,
X2 = X3 = 0,
```

the flat curl is zero, but the transported curl satisfies

```text
N(curl_q) = 1073741824/4503599761588225.
```

At cross charge `C=6`, `(rho/36)C=1/49152`, and

```text
N(curl_q) - (1/49152)^2
  = 2589569785603817471
    /10880332700790838158950400
  > 0.
```

This does not refute the desired selected-background theorem because no Euler–Lagrange equation is assumed. It proves that radius plus flat cancellation is insufficient.

Formal owner:

```text
BalabanP33CovariantCurlRadiusStressTestExact.agda
```

## 8. Einstein–Cartan–Yang–Mills source audit

Round 35 also records, without importing their conclusions, Emmanouil Karolos Čižek’s:

- *A Constructive Einstein–Cartan–Yang–Mills Theory with Positive Mass Gap in Four Dimensions*, DOI `10.5281/zenodo.17246443`;
- structural overview, DOI `10.5281/zenodo.17718647`;
- regulated slab paper, DOI `10.5281/zenodo.18280110`.

The formal audit distinguishes:

```text
Einstein-Cartan-Yang-Mills theory,
pure four-dimensional Yang-Mills,
auxiliary boundary Langevin generator,
boundary slab transfer kernel,
reconstructed physical Hamiltonian.
```

It proves that none of these theory/operator promotions is definitional. The first monograph bridge is exact torsion/gravity-sector decoupling to pure Yang–Mills. The slab route remains conditional on an ultraviolet continuum construction on `R4` and a physical operator identification.

Formal owner:

```text
YangMillsCizekEinsteinCartanClaimAuditExact.agda
```

## 9. Exact remaining Gate-I frontier

The shortest remaining sequence is now:

```text
physicalSelectedFactorEnvelopeInstantiation
variationalEulerLagrangeEquationAtSelectedBackground
selectedBackgroundRegularityControlsPlaquetteCurvature
selectedBackgroundCorrelatedWilsonLower
physicalDeepWilsonRemainderLower
selectedBackgroundPhysicalWLocal
selectedBackgroundHessianOneThirtySecond
```

The refined numerical targets are:

```text
-(rho/36) C_p(h)
  <= correlatedSingletonPairPart_p(A,h),

-(rho/144) q_p(h)
  <= deepTripleQuarticRemainder_p(A,h).
```

The deep coefficient arithmetic and generic quaternion theorem are complete; its remaining step is the literal physical envelope. The correlated inequality still requires the selected Euler–Lagrange/regularity theorem. The stress test rules out replacing that theorem by a radius-only estimate.

After these close, the existing composition yields

```text
H_A[h,h] >= 10739/196608 ||h||^2
           >= 1/32 ||h||^2.
```

The next gate is then the literal Hessian matrix, Hermiticity, finite stencil, row/column interaction mass, constructive inverse, physical Combes–Thomas decay and one scale-uniform RG step.
