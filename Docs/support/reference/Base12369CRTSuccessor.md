# Base12369 identity, CRT, depth, and successor hierarchy

This extension separates the roles

```text
1 = identity
2 = binary polarity/parity
3 = triadic phase
6 = 2 * 3 coupling
9 = 3^2 depth
27 = 3^3 depth
```

Six does not generate one or two in the non-unital `+`/`*` grammar. It exposes
a two-state factor after factorisation or projection is admitted.

The implementation distinguishes the existing half-turn orientation factor from
the canonical CRT coordinate:

```text
C6 ≅ C2 × C3,   k ↦ (k mod 2, k mod 3).
```

These are not the same projection: orientation groups `0,1,2` versus `3,4,5`,
while CRT parity alternates around the six-cycle.

`Resolution23Q` generalises the lattice to `2^a * 3^b * q^c`. Primality of `q`
and pairwise-coprime witnesses remain explicit prerequisites for a general CRT
theorem.

The exact finite arithmetic is

```text
47 * 59 * 71 = 196883
1 + 196883 = 196884.
```

`19883` is not treated as equivalent. These equalities do not by themselves
promote Monster or modular-j authority.

Three typed uses of `j` are separated: compiled chart index, modular invariant,
and representation/spin label. In the chart lane, `j+1` is a successor/rechart
operation available when the cached inverse at `j` stops gluing; it is not proof
that overflow occurred.
