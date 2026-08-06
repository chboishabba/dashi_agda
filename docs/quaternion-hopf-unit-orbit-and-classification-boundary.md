# Quaternionic Hopf unit orbits and classification boundaries

This addendum records the final two proof surfaces added to the Hurwitz–Hopf–Noether cross-pollination tranche.

## Exact unit-quaternion orbit invariance

`DASHI/Mathematics/Topology/QuaternionHopfUnitOrbitExact.agda` works on the same rational quaternion carrier used by the Yang–Mills Wilson-Hessian implementation.

For a quaternion pair `(a,b)` and quaternion `u`, simultaneous right multiplication is

```text
(a,b) |-> (a u,b u).
```

The module proves the exact polynomial identities

```text
HopfQuaternion(a u,b u)
  = N(u) HopfQuaternion(a,b),

HopfScalar(a u,b u)
  = N(u) HopfScalar(a,b).
```

It then packages a unit quaternion as a quaternion with proof `N(u)=1`, proves closure under multiplication from the existing quaternion norm-composition theorem, and instantiates the generic Klein action interface. The scalar Hopf coordinate and all four quaternion coordinates are invariant observables on witnessed unit-quaternion orbits.

The right action is represented honestly: the generic action law is left-oriented, so composition in the action record reverses the ordinary quaternion multiplication order.

This proves one direction of the classical fibre picture:

```text
same witnessed unit-quaternion orbit
=> same Hopf coordinates.
```

It does not prove the converse, smooth local triviality, fibre completeness, or a principal-bundle theorem.

Primary source metadata in the Agda header:

- Heinz Hopf, *Über die Abbildungen der dreidimensionalen Sphäre auf die Kugelfläche*, DOI `10.1007/BF01457962`;
- John C. Baez, *The Octonions*, DOI `10.1090/S0273-0979-01-00934-X`.

## Frobenius and Hurwitz classification theorem boundary

`DASHI/Mathematics/Algebra/HurwitzFrobeniusClassificationBoundary.agda` separates the exact rational polynomial evidence from the historical real classification theorems.

The Frobenius boundary requires explicit fields for:

```text
real vector-space structure,
finite dimension,
associative real-algebra laws,
unit,
division.
```

Its conclusion requires both an indexed dimension witness in `{1,2,4}` and a real-algebra classification isomorphism to `R`, `C`, or `H`.

The Hurwitz boundary requires explicit fields for:

```text
real vector-space structure,
finite dimension,
real algebra laws,
positive-definite quadratic norm,
norm composition,
division.
```

Its conclusion requires both an indexed dimension witness in `{1,2,4,8}` and a norm-preserving classification by `R`, `C`, `H`, or `O`.

No inhabitant of either theorem record is supplied. A separate bridge record lists the missing real-analytic and exhaustive-classification evidence needed beyond the concrete rational quaternion and octonion identities.

Primary source metadata in the Agda header:

- Adolf Hurwitz, *Über die Komposition der quadratischen Formen*, DOI `10.1007/BF01448439`;
- Matej Brešar and Victor S. Shulman, *On, around, and beyond Frobenius' theorem on division algebras*, DOI `10.1080/03081087.2020.1761281`;
- Aleksandra Gałecka, *A Proof of the Hurwitz Theorem About Composition Algebras*, DOI `10.24917/20809751.13.4`.

## Validation ownership

Both modules are imported by

```text
DASHI.Mathematics.CrossPollination.HurwitzHopfNoetherMillenniumCrossPollinationValidation
```

and guarded by

```text
scripts/check_hurwitz_hopf_noether_millennium_crosspollination.sh.
```

The final checker target remains

```text
DASHI.EverythingHurwitzHopfNoetherCrossPollination
```

which imports the repository-wide `DASHI.Everything` aggregate and the full cross-pollination validation root. Until the pinned Agda 2.9 checker produces an observed success receipt, the draft PR remains unverified.
