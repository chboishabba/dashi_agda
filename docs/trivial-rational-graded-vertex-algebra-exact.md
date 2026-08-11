# Exact rational graded vertex-algebra seed

`DASHI/Moonshine/TrivialRationalGradedVertexAlgebraExact.agda` supplies a concrete proof-bearing example beneath the general graded-VOA boundary.

The grading is:

```text
V_0 = Q,
V_n = {0} for n>0.
```

The vacuum is `1`, the conformal vector is `0` in grade two, and the mode operation is

```text
a_(-1)b = ab,
a_n b = 0 for n != -1.
```

The module proves directly over the rational ring:

```text
1_(-1)b = b,
a_(-1)1 = a,
positive vacuum modes vanish,
positive creation modes vanish,
a_(-1)b = b_(-1)a,
a_(-1)(b_(-1)c) = (a_(-1)b)_(-1)c,
distributivity,
translation is zero and is a derivation,
all conformal-vector modes vanish.
```

These witnesses are collected in `TrivialRationalVertexAlgebraCertificate`.

This closes the gap between merely naming VOA axioms and having at least one exact local inhabitant. It does not identify the example with the Monster VOA `V^natural`, and it does not prove the general Jacobi/Virasoro theory, rationality, C2-cofiniteness, modularity, or genus zero.

Source metadata in the Agda header includes:

- Victor Kac, *Vertex Algebras for Beginners*; no DOI asserted for the cited book edition;
- Richard Borcherds, *Vertex algebras, Kac-Moody algebras, and the Monster*, DOI `10.1073/pnas.83.10.3068`.
