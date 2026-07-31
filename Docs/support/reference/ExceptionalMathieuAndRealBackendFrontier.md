# Exceptional Mathieu and exact-real backend frontier

This tranche deliberately separates two dependency lanes:

```text
explicit ternary code
  -> complete symbol enumerator
  -> S(5,6,12)
  -> transported M12 design action
  -> signed 2.M12 code action

pi continued fractions
  -> provenance-indexed rational constants
  -> narrow pi/Y interval interface
  -> versioned TAX/NRCI claims
```

The finite exceptional lane does not depend on Bishop reals.

## Explicit finite results

The existing systematic `[12,6,6]_3` construction is extended with the full three-symbol composition enumerator:

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

Puncturing any coordinate gives the same independently checked distribution:

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
```

and

```text
729 * 243 = 3^11 = 177147.
```

The independent standard-library Python oracle constructs every error sphere and verifies that their union has exactly `3^11` elements.

## Self-duality boundary

The explicit code already supplies:

- a systematic left inverse and injective encoder;
- a zero Gram matrix;
- every enumerated codeword orthogonal to all six generator rows;
- half-dimension arithmetic `6+6=12`.

`SelfDualityFiniteBoundary.agda` exposes the reusable theorem that a half-dimensional self-orthogonal finite subspace is self-dual. The remaining local seam is representation, not mathematics: the ad hoc `Vec12` API does not yet expose first-class `rowSpan`, `dual` and `dimension` objects against which the generic theorem can be instantiated. This remains fail-closed rather than using uniqueness to prove self-duality.

## Transported Mathieu action

The compact two-generator presentation is attributed to:

- John Leech, *A Presentation of the Mathieu Group M12*, DOI `10.4153/CMB-1969-005-8`.

Its published coordinate labelling is not assumed to equal the local code labelling. The checked transport is:

```text
q = (0,9,3,1,5,7,2,10,8,11,6,4).
```

After conjugation, the local support permutations are:

```text
S = (1 5 7 2 10 8 11 6 4 9 3)
T = (0 9)(1 5)(2 10)(3 4)(6 7)(8 11).
```

The Agda finite surface checks that both preserve all 132 locally computed hexads and that thirteen closure rounds from one transported seed recover all 132 blocks. The dependency-free oracle additionally enumerates the generated permutation group and obtains order `95040`.

## Why signs are necessary

The support permutations do not preserve the oriented ternary codeword set on their own. Explicit sign vectors give monomial lifts:

```text
dS = (1,1,2,2,1,1,2,2,2,1,1,2)
dT = (1,2,2,1,2,1,1,2,1,2,1,2).
```

The Agda module checks both lifts against all 729 codewords. The lifted `T` has order four:

```text
T_lift^2 = -I,
```

and central negation has order two.

The oracle enumerates the signed group with order `190080` and checks that the induced six-dimensional `F3` module is irreducible: every one of the 728 nonzero vectors generates the full six-dimensional module under the two induced matrices.

The external identification with `M12` and `2.M12` is calibrated by:

- John H. Conway, Noam D. Elkies and Jeremy L. Martin, *The Mathieu Group M12 and Its Pseudogroup Extension M13*, DOI `10.1080/10586458.2006.10128958`.

Group isomorphism is not silently replaced by an order calculation.

## Stabilizer correction

The order-660 ambiguity is resolved as follows:

```text
|M12|                    = 95040
point stabilizer         = 95040/12      = 7920
ordered two-point stab.  = 95040/(12*11) = 720
L2(11) maximal in M11    = 7920/12       = 660
```

Therefore `660` is not the ordered two-point stabilizer and is not produced by puncturing twice. It is the order of a distinct index-12 maximal subgroup of `M11`, as calibrated by the ATLAS of Finite Group Representations.

## Observer-constant identity fork

Three identities are now distinct:

```text
craig-v5-4-1-source
canonical-pi-cf-50
exact-pi-target
```

The exact rational sensitivity is recorded:

```text
Y_Craig - Y_CF =
2734787287797861895878337337413165344545354810381555572709194
/
1449569606998549182495542391376708973611508633517180526971395851214621946728005627560091575061157712043175668851961.
```

Historical UBP calculations remain reproducible, corrected canonical calculations are possible, and neither finite rational is promoted to the exact irrational target.

## Exact-real backend roles

The architecture distinguishes:

1. Bishop regular sequences for preserving and migrating the existing theorem corpus;
2. narrow rational enclosures for the specific pi/Y certificate;
3. a Cubical HoTT-real prototype for a future hard analytic archetype.

Sources are attached as:

- Zachary Murray, *Constructive Analysis in the Agda Proof Assistant*, DOI `10.48550/arXiv.2205.08354`;
- Jackson Brough, *Formalizing the Real Numbers in Homotopy Type Theory with Cubical Agda*, DOI `10.48550/arXiv.2604.24782`;
- `viktorcsimma/bishop`, repository source with no DOI.

The Bishop migration first tests whether constructor-level absolute-value idempotence gives the representation equality needed for `K-abs`. Rational equivalence alone is not treated as sufficient because `K` observes a concrete representation. If the computation lemma fails, the formal fallback is a common-index regularity proof.

## TAX dynamics

Before any complete-Lyapunov promotion, a concrete certified Leech move system must instantiate:

- a finite transition graph;
- exact decreasing/constant/increasing TAX edge classes;
- strongly connected components;
- a quotient DAG;
- constant TAX on recurrent components and strict decrease between them.

The conceptual source is Peter Giesl, Zachary Langhorne, Carlos Argáez and Sigurdur Hafstein, *Computing complete Lyapunov functions for discrete-time dynamical systems*, DOI `10.3934/dcdsb.2020331`.

For the first finite Leech model this is an exact graph problem; numerical meshfree or RKHS methods are not prerequisites.

## Validation authority

Three authority levels remain explicit:

1. Agda-reducible finite checks;
2. dependency-free exhaustive Python oracle checks;
3. cited external theorem/group identifications.

The oracle is not a substitute for the Agda kernel, and citations are not proof terms. The pull request should remain draft until both frontier regression aggregates receive green Agda 2.9 receipts.
