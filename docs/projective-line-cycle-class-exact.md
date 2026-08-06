# Exact projective-line cycle-class model

`DASHI/Mathematics/AlgebraicGeometry/ProjectiveLineCycleClassExact.agda` gives a concrete codimension-one positive case beneath the general Hodge boundary.

The finite model identifies both rational divisor cycles and rational `H^(1,1)` classes with `Q`:

```text
cycleClass(q [point]) = q.
```

It proves exactly:

```text
cycleClass(0)=0,
cycleClass(C+D)=cycleClass(C)+cycleClass(D),
cycleClass(qC)=q cycleClass(C),
every rational H^(1,1) class has a cycle representative,
the point cycle represents the generator 1.
```

The witnesses are collected in `P1CycleClassCertificate`.

This is an exact local model of the Hodge conjecture in codimension one for `P^1`. It remains separate from constructing singular/de Rham cohomology for a smooth projective variety and from any higher-dimensional Hodge-conjecture claim.
