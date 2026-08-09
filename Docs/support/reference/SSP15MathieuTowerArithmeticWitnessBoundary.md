# Mathieu tower: arithmetic witness boundary

`DASHI.Moonshine.MathieuStabilizerTowerExact` proves the exact order/index spine

```text
8 --x9--> 72 --x10--> 720 --x11--> 7920 --x12--> 95040.
```

The implementation deliberately uses the names

```text
OrbitStabilizerArithmeticWitness
MathieuStepArithmeticWitness
```

rather than `PointedOrbitFibration` or `MathieuStepRealization`.

An order equation

```text
|G| = |orbit| * |stabilizer|
```

is necessary but not sufficient to construct a group action. A genuine realization would additionally require finite carriers, a group structure on the transformation carrier, an action law, a chosen point, a definition of its stabilizer, finite-cardinality equivalences, and a proof that the stabilizer inclusion and orbit quotient have the stated sizes.

The Round-6 record therefore contains only the three natural-number orders and their multiplication law. `stepArithmeticWitness` packages each exact Mathieu order equation into that type. The actual Mathieu action and point-stabilizer identifications remain source-bounded external authority.

The same boundary prevents the order-eight factor from being silently identified with the square-grid group `D4`. The Atlas-reported stabilizer is tagged as quaternion `Q8`; equality of orders does not imply isomorphism.

Primary sources:

- John H. Conway, Robert T. Curtis, Simon P. Norton, Richard A. Parker, and Robert A. Wilson, *Atlas of Finite Groups*, Oxford University Press, 1985. No DOI assigned.
- John D. Dixon and Brian Mortimer, *Permutation Groups*, Springer, 1996. DOI `10.1007/978-1-4612-0731-3`.
