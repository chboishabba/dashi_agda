# Triadic arithmetic–spectral assembly

## Status

This tranche implements the layered route

```text
balanced-trit filtration
  -> exact finite quotients
  -> carry arithmetic and finite symmetries
  -> character / irrep codecs
  -> sector traces and finite q-series prefixes
  -> gated modular / Eisenstein / Hecke coordinates
  -> gated elliptic j-moduli coordinates
  -> certified inverse limits and analytic bounds
  -> joint representation/depth MDL
```

The implementation deliberately does **not** force every theorem through one analytic object. Exact finite structure is checked at each quotient depth; infinite, modular, elliptic, and statistical conclusions require their own typed certificates.

## Existing DASHI spine consumed

The new modules extend rather than replace the established repo surfaces:

- `DASHI.Foundations.Base369FiniteRingLaws`
- `DASHI.Foundations.SSPTritCarrier`
- `DASHI.Foundations.SSPPrimeLane369Refinement`
- `DASHI.Foundations.SSPPrimeLaneUnitAction`
- `DASHI.Geometry.SSP369Ultrametric`
- `DASHI.Geometry.SSP369TreeAutomorphism`
- `DASHI.Physics.Closure.SSPPrimeLane369PAdicBridge`
- `DASHI.Physics.Closure.SSPPrimeLane369PAdicUltrametricBridge`
- `DASHI.Physics.Closure.BalancedTernaryContinuousEnvelope`

The established SSP/Base369 lane continues to supply the repository’s prime-lane, unit-action, depth-address, and prefix-ultrametric vocabulary. The present tranche adds the canonical finite `3^n` quotient tower and the arithmetic/spectral consumers needed by the continuous-envelope programme.

## 1. Exact finite quotient tower

`DASHI.Foundations.TriadicFiniteQuotient` represents

```text
Z / 3^n Z
```

by the canonical balanced-trit carrier `TritPrefix n`. It supplies:

- `pow3 n`;
- a numeric residue representative with `neg -> 2`, `zer -> 0`, `pos -> 1`;
- projection of a stream to its first `n` trits;
- reduction `3^(n+1) -> 3^n` by dropping the highest retained digit;
- a canonical zero-section lift;
- exact reduction/projection compatibility;
- the inverse-limit carrier `TriadicInverseLimitPoint`;
- compatible finite kernel families and their induced inverse-limit action.

The quotient topology is represented directly by prefix/cylinder agreement. No analytic completion is inferred from the finite tower.

## 2. Concrete carry arithmetic

`DASHI.Algebra.TriadicFiniteArithmetic` implements balanced-ternary addition modulo `3^n` using a finite carry full-adder. Overflow above the retained depth is discarded, as required by the quotient.

Checked now:

- the half-adder and full-adder tables;
- finite-depth addition;
- zero residue;
- digitwise additive inverse;
- left identity;
- left inverse;
- canonical arithmetic examples such as `1 + 1 = -1 mod 3` and `4 + 4 = -1 mod 9`.

Explicit remaining arithmetic law receipt:

- associativity;
- commutativity;
- compatibility of reduction with addition.

These are isolated in `TriadicArithmeticLawReceipt`, rather than assumed silently.

## 3. Additive characters, irreps, unit actions, and affine symmetry

`DASHI.Algebra.TriadicFiniteIrrep` defines:

- the finite additive-group interface on the depth quotient;
- a cyclotomic/phase target;
- one-dimensional additive characters;
- exact signal/spectrum codecs with pointwise reconstruction;
- translation actions;
- translation-invariant kernels;
- block decomposition, block preservation, Parseval, and spectral-tail proof slots;
- the full finite character-transform bundle.

It includes an exact identity codec and a trivial phase character as checked baselines. They validate the reconstruction and character-law interfaces, but are not presented as a cyclotomic DFT.

`DASHI.Algebra.TriadicFiniteAffineAction` adds:

- a finite unit-group action on the additive quotient;
- compatibility with quotient addition;
- the affine semidirect carrier `(translation, unit)`;
- affine action on residues;
- affine kernel-equivariance receipts.

Thus the symmetry lane covers the three intended levels:

```text
additive translations
unit-group automorphisms
affine semidirect actions
```

## 4. Irrep traces and q-series

`DASHI.Physics.Closure.TriadicIrrepTraceBridge` ties a stable representation sector to a finite block operator at every depth and requires its trace to equal the corresponding q-series coefficient.

`DASHI.Physics.Closure.TriadicSectorQSeries` supplies:

- an exact coefficient algebra interface;
- sector trace towers;
- finite q-series prefixes;
- an exact finite prefix codec;
- rational-recurrence gates;
- Hecke probes;
- p-adic congruence gates.

A sequence of traces is not automatically a modular form. These gates record the tests required before promotion.

## 5. Modular, Eisenstein, Hecke, and p-adic families

`DASHI.Physics.Closure.TriadicModularAutomorphicGate` makes the modular entry condition explicit.

A `ModularTransformationGate` must supply:

- a parameter domain;
- modular elements and their action;
- the automorphy factor;
- weight and level;
- the transformation law;
- agreement between the analytic object and the tracked finite coefficients.

Only after that gate may an `EisensteinBasisGate` supply:

- Eisenstein and cusp basis indices;
- finite coordinates;
- coefficient functions;
- exact coefficient reconstruction;
- finite-dimensionality and independence receipts.

Hecke eigenstructure and p-adic weight interpolation are separate gates. `AutomorphicCompressionReceipt` requires exact recovery of all tracked coefficients from the latent modular coordinates.

This prevents a partition function, theta candidate, trace series, or orbit count from being called “Eisenstein” merely because it is a q-series.

## 6. Elliptic origin and j-invariant quotient

`DASHI.Geometry.TriadicEllipticModuliGate` does not assign a j-invariant to a raw stream. It first requires an `EllipticOriginGate`:

- a source object, such as a spectral curve or genus-one action level set;
- a derived curve presentation;
- a genus-one receipt;
- a chosen base point;
- a Weierstrass conversion.

For a short Weierstrass datum `y^2 = x^3 + A x + B`, the j relation is recorded without division:

```text
(4 A^3 + 27 B^2) * j = 1728 * 4 A^3.
```

A nonsingularity receipt is mandatory. Coordinate-change invariance and orbit equality are separate certificates. `EllipticModuliCompression` also retains extra level structure because `j` alone need not reconstruct the original presentation.

This gives j the intended role:

```text
raw presentation
  -> associated elliptic object
  -> coordinate-change orbit
  -> j quotient plus retained level data
```

It does not real-smoothify native `Z_3`.

## 7. Analytic certificates and verified limits

`DASHI.Physics.Closure.TriadicAnalyticCertificates` separates:

- uniform geometric-tail convergence;
- quantitative first-difference/injectivity bounds;
- compact-to-Hausdorff topology and Cantor-image recovery;
- weighted infinite-axis summability;
- native p-adic analytic-manifold structure.

The intended Euclidean tail is the familiar bound

```text
|Phi(d) - Phi_n(d)| <= lambda^n / (1 - lambda),  0 < lambda < 1.
```

The intended separation lower bound for `lambda < 1/3` and first difference at depth `n` is

```text
((1 - 3 lambda) / (1 - lambda)) lambda^n
  <= |Phi(x) - Phi(y)|.
```

The certificate interface records these formula obligations without pretending the repository already has a canonical real ordered-complete-field implementation.

`DASHI.Physics.Closure.TriadicVerifiedLimitAssembly` combines:

- an inverse-limit point;
- a compatible kernel family;
- a continuous envelope;
- depth-tail certificates;
- uniform convergence and quantitative topology;
- weighted-axis summability;
- character transforms linked to block traces;
- a trace q-series;
- mode stabilization;
- optional modular and elliptic gates;
- a native p-adic analytic-manifold certificate;
- an explicit proof that real smoothness of native `Z_3` is not required.

## 8. Joint representation/depth MDL

`DASHI.Physics.Closure.TriadicRepresentationMDL` selects over both depth and representation family:

- raw trits;
- finite quotient coordinates;
- irrep blocks;
- certified modular coordinates;
- elliptic moduli plus retained level data.

The finite objective is

```text
representation cost + residual cost.
```

`BoundedRepresentationMDL` is an exact finite minimizer receipt. Asymptotic statements are kept separate in `RepresentationMDLConsistencyGate`, which requires:

- a stochastic data law;
- a Kraft-valid or prefix-free code;
- identifiability or an oracle condition;
- controlled model-class growth;
- concentration or ergodicity;
- risk consistency;
- true-depth recovery only where identifiable.

## Assembly and regression surfaces

`DASHI.Physics.Closure.TriadicArithmeticSpectralAssembly` imports the existing repo spine and the full new tranche. Its status record distinguishes implemented carriers/gates from unproved promoted theorems.

`DASHI.Physics.Closure.TriadicArithmeticSpectralRegression` checks canonical finite witnesses for:

- stream projection and quotient reduction;
- inverse-limit compatibility;
- carry arithmetic;
- additive inverse;
- exact identity spectral reconstruction;
- a finite q-series prefix;
- bounded MDL depth indices;
- the continued rejection of a real-smooth `Z_3` promotion.

## Claim matrix

| Claim | Current status |
|---|---|
| Exact finite balanced-trit quotient carrier | implemented |
| Reduction and inverse-limit point | implemented |
| Concrete carry addition modulo `3^n` | implemented |
| Zero identity and additive inverse | checked |
| Associativity, commutativity, reduction/addition law | explicit receipt |
| Exact finite spectral codec interface | implemented |
| Genuine cyclotomic DFT and orthogonality | gated |
| Unit and affine actions | implemented interfaces |
| Block traces to q-series coefficients | explicit bridge |
| Finite q-series prefixes | implemented |
| Rational recurrence / Hecke / p-adic congruence | gated |
| Modular transformation law | gated |
| Eisenstein/cusp reconstruction | gated behind modular law |
| Elliptic origin | gated |
| Division-free j relation and orbit receipt | implemented interface |
| Uniform convergence and geometric tail | explicit analytic certificate |
| Quantitative injectivity/topology | explicit analytic certificate |
| Weighted infinite-axis summability | explicit analytic certificate |
| Native p-adic analytic manifold | explicit non-Archimedean certificate |
| Real smooth manifold structure on native `Z_3` | rejected |
| Bounded representation/depth MDL minimum | implemented receipt |
| Statistical MDL consistency | gated |

## Recommended proof order

1. Discharge `TriadicArithmeticLawReceipt` by carry-locality induction.
2. Instantiate the exact cyclotomic phase ring and additive character table at finite depth.
3. Prove character orthogonality, completeness, and exact DFT reconstruction.
4. Instantiate a translation-invariant kernel and prove block diagonalization plus Parseval.
5. Bind stable block traces to a concrete q-series and test recurrence/congruence laws.
6. Attempt a modular transformation theorem only for a justified theta, partition, or spectral trace object.
7. Introduce Eisenstein/Hecke coordinates only after Step 6.
8. Construct an elliptic origin only when a genuine genus-one spectral or action curve appears.
9. Instantiate real analytic tail/topology certificates and weighted-axis limits.
10. Instantiate bounded MDL, then separately prove Kraft and statistical consistency assumptions.
