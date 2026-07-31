# Exceptional Mathieu and exact-real backend frontier

This tranche deliberately separates two dependency lanes:

```text
explicit ternary code
  -> reusable finite F3 subspaces
  -> concrete self-duality
  -> complete symbol enumerator
  -> S(5,6,12)
  -> transported M12 design action
  -> signed 2.M12 code action

pi continued fractions
  -> provenance-indexed rational constants
  -> rational antitone certificates
  -> exact-real embedding boundary
  -> versioned TAX/NRCI claims
```

The finite exceptional lane does not depend on Bishop reals.

## Reusable finite-linear layer

`DASHI/Foundations/FiniteLinear/F3Subspace.agda` introduces the smallest first-class API required by demonstrated consumers:

- finite `F3Space` carriers;
- `F3Subspace` predicates with zero/additive/scalar closure;
- inclusion and extensional subspace equality;
- `F3LinearMap`;
- kernel and image subspaces;
- reusable finite dot/add/scale algebra.

It deliberately does not attempt a universal field/rank hierarchy before the current theorem graph needs one.

A second non-code consumer, `AntiDiagonalKernel.agda`, proves that the sum-zero line in `F3²` is exactly the image of the anti-diagonal embedding

```text
t |-> (t,-t).
```

This exercises the same kernel/image/inclusion API used by the Golay construction and connects to diagonal/off-diagonal channel decompositions without importing coding-specific assumptions.

## Concrete ternary Golay self-duality

The explicit code now supplies more than a readiness boundary.

`GolaySelfDualSubspace.agda` represents:

```text
C    = image of the systematic encoder
Cperp = all words orthogonal to every codeword
```

as first-class `F3Subspace` predicates. It proves:

1. the six-row linear-combination encoder equals the existing systematic encoder;
2. every encoded word is orthogonal to all generator rows;
3. every codeword lies in `Cperp`;
4. every word in `Cperp` has a systematic dual normal form determined by its final six coordinates;
5. that normal form is again an encoded codeword;
6. therefore `C = Cperp` by mutual inclusion.

The two finite presentation identities are checked over the complete 729-message carrier. Uniqueness of the ternary Golay equivalence class is not used to infer self-duality.

The source calibration remains:

- F. Jessie MacWilliams and N. J. A. Sloane, *The Theory of Error-Correcting Codes*, no DOI recorded for the cited book;
- F. Jessie MacWilliams, Colin L. Mallows and N. J. A. Sloane, *Generalizations of Gleason's theorem on weight enumerators of self-dual codes*, DOI `10.1109/TIT.1972.1054898`;
- Vera Pless, *More on the uniqueness of the Golay codes*, DOI `10.1016/0012-365X(92)90569-2`.

## Explicit finite results

The systematic `[12,6,6]_3` construction has the full three-symbol composition enumerator:

```text
(n0,n1,n2)  coefficient
(12,0,0)      1
(6,6,0)      22
(6,0,6)      22
(6,3,3)     220
(3,6,3)     220
(3,3,6)     220
(0,12,0)      1
(0,6,6)      22
(0,0,12)      1
```

Puncturing any coordinate gives the independently checked distribution:

```text
weight 0   1
weight 5   132
weight 6   132
weight 8   330
weight 9   110
weight 11  24
```

For the final-coordinate puncture, the Agda module computes that distribution and the derived `S(4,5,11)` design: 66 five-element blocks and unique coverage of all 330 tetrads.

The radius-two sphere volume is

```text
1 + 11*2 + C(11,2)*2^2 = 243,
729 * 243 = 3^11 = 177147.
```

The dependency-free oracle constructs every error sphere and verifies that their union has exactly `3^11` elements.

## Transported Mathieu action

The compact two-generator presentation is attributed to:

- John Leech, *A Presentation of the Mathieu Group M12*, DOI `10.4153/CMB-1969-005-8`.

Its published coordinate labelling is transported by

```text
q = (0,9,3,1,5,7,2,10,8,11,6,4).
```

The local support permutations are:

```text
S = (1 5 7 2 10 8 11 6 4 9 3)
T = (0 9)(1 5)(2 10)(3 4)(6 7)(8 11).
```

The Agda finite surface checks preservation of all 132 locally computed hexads and recovery of the full design orbit. The oracle obtains permutation-group order `95040`.

The support permutations need sign lifts to preserve oriented ternary codewords:

```text
dS = (1,1,2,2,1,1,2,2,2,1,1,2)
dT = (1,2,2,1,2,1,1,2,1,2,1,2).
```

The lifted `T` satisfies `T_lift^2 = -I`; the oracle obtains signed-group order `190080` and checks computational irreducibility of the induced six-dimensional `F3` module.

The external identification with `M12` and `2.M12` is calibrated by:

- John H. Conway, Noam D. Elkies and Jeremy L. Martin, *The Mathieu Group M12 and Its Pseudogroup Extension M13*, DOI `10.1080/10586458.2006.10128958`.

Group isomorphism is not replaced by an order calculation.

## Stabilizer correction

```text
|M12|                    = 95040
point stabilizer         = 95040/12       = 7920
ordered two-point stab.  = 95040/(12*11)  = 720
L2(11) maximal in M11    = 7920/12        = 660
```

Thus `660` is not the ordered two-point stabilizer and is not produced merely by puncturing twice.

## Rational certificate first

`RationalCertificateTransport.agda` exposes the backend-independent principle:

```text
prove the ordered finite inequality in Q
then transport the certificate through an exact-real embedding.
```

It contains:

- generic antitone interval transport;
- rational interval and point-containment records;
- the observer map `f(x)=x/(x^2+2)`;
- the exact factorisation

```text
x*(y*y+2) - y*(x*x+2) = (y-x)*(x*y-2);
```

- a positive cross-multiplication interface;
- canonical continued-fraction rational endpoints around the canonical 50-coefficient convergent;
- candidate `Y` endpoints obtained by reversing the source interval through the antitone observer map;
- an exact-real embedding/containment interface.

The constructive `pi` containment theorem remains a genuine open instantiation. Neither the source nor canonical finite rational is promoted to exact `pi` or exact `Y`.

## Completed Bishop absolute-product seam

The previous migration decision tree has resolved to its narrow branch.

Bishop commit

```text
d732b0340d729b264227a70fcf38383d8fb3ac3c
```

contains:

```text
K-abs
K-abs-index
seq-abs-mul-index
```

and advances the original real absolute-product theorem by aligning the multiplication sampling indices through the actual unnormalised rational representation.

The Dashi master pin is

```text
7b31431846ede85473454bf4cc57f5fa5d050a95.
```

Reported validation is:

- `RealProperties.agda`: passed;
- `Inverse.agda`: passed;
- `Sequence.agda`: passed;
- `git diff --check`: passed.

`BishopAbsMigrationReceipt.agda` records this as a successful compatibility result. Common-index transport is not required for this theorem; it remains a future fallback only for operations that genuinely select different modulus indices.

The source attribution is:

- Zachary Murray, *Constructive Analysis in the Agda Proof Assistant*, DOI `10.48550/arXiv.2205.08354`;
- Viktor Csimma and contributors, `bishop: Constructive Analysis in Agda`, repository source with no DOI.

This does not assert that Bishop regular sequences are the universally optimal executable exact-real backend.

## Observer-constant identity fork

The following remain distinct:

```text
craig-v5-4-1-source
canonical-pi-cf-50
exact-pi-target
```

Historical UBP calculations remain reproducible, corrected canonical calculations are possible, and neither finite rational is promoted to the exact irrational target.

## TAX dynamics

Before any complete-Lyapunov promotion, a concrete certified Leech move system must instantiate:

- a finite transition graph;
- exact decreasing/constant/increasing TAX edge classes;
- strongly connected components;
- a quotient DAG;
- constant TAX on recurrent components and strict decrease between them.

The conceptual source is Peter Giesl, Zachary Langhorne, Carlos Argáez and Sigurdur Hafstein, *Computing complete Lyapunov functions for discrete-time dynamical systems*, DOI `10.3934/dcdsb.2020331`.

Endpoint TAX differences remain exact gradients; any genuinely nontrivial path circulation requires a separate edge observable.

## Validation authority

Three authority levels remain explicit:

1. Agda-reducible finite checks;
2. dependency-free exhaustive Python oracle checks;
3. cited external theorem/group identifications.

The oracle is not a substitute for the Agda kernel, and citations are not proof terms. The pull request remains draft until both updated frontier regression aggregates receive green Agda 2.9 receipts.
