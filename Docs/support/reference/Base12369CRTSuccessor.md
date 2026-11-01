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
C6 ≅ C2 × C3,   k ↦ (k mod 2, k mod 3).
These are not the same projection: orientation groups `0,1,2` versus `3,4,5`,
while CRT parity alternates around the six-cycle.
`Resolution23Q` generalises the lattice to `2^a * 3^b * q^c`. Primality of `q`
and pairwise-coprime witnesses remain explicit prerequisites for a general CRT
theorem.
The exact finite arithmetic is
47 * 59 * 71 = 196883
1 + 196883 = 196884.
`19883` is not treated as equivalent. These equalities do not by themselves
promote Monster or modular-j authority.
Three typed uses of `j` are separated: compiled chart index, modular invariant,
and representation/spin label. In the chart lane, `j+1` is a successor/rechart
operation available when the cached inverse at `j` stops gluing; it is not proof
that overflow occurred.
## Status
This is a finite typed extension of the Base369 polyphase tranche. It separates
number roles rather than treating visible numerals as interchangeable evidence.
## Core hierarchy
The canonical role reading is:
1 = identity / neutral carrier
2 = binary polarity or parity carrier
3 = triadic phase carrier
6 = 2 * 3 binary-triadic coupling
9 = 3^2 triadic depth
27 = 3^3 next triadic depth
Six does not generate one and two in the non-unital `+`/`*` expression grammar.
It exposes a two-state factor once factorisation, projection, or CRT coordinates
are admitted.
## Two different factorisations of HexTruth
The repository now distinguishes:
1. the existing orientation factor
HexTruth ≅ TriTruth × OrientationPolarity
where `0,1,2` and `3,4,5` form positive/negative half-turn blocks; and
2. the Chinese-remainder coordinate
C6 ≅ C2 × C3
k ↦ (k mod 2, k mod 3)
where parity alternates around the six-cycle.
These are both useful, but they are not the same projection. The CRT module
checks encode/decode round trips and keeps full group-isomorphism promotion
behind a separate law receipt.
## Mixed factor-depth coordinates
`Resolution23Q` generalises the existing resolution lattice to
2^a * 3^b * q^c.
The three refinement operations commute definitionally. The `q` coordinate is
a raw factor axis: primality and pairwise coprimality must be supplied by
separate witnesses before a CRT product theorem is promoted.
Canonical examples include `1,2,3,6,9,27`. In particular, `27 = 3^3` is a
third-depth triadic carrier, not a product `C3 × C3 × C3` unless that product
carrier is deliberately selected.
## 196883, 196884, and +1
The exact finite arithmetic is:
The shorter glyph `19883` is not treated as equivalent. The checked arithmetic
is role-separated from Monster representation and modular-j authority.
The `+1` can mean either:
- an identity/one-dimensional summand in a finite decomposition; or
- a successor/overflow move from chart `j` to chart `j+1`.
Those meanings are deliberately not collapsed.
## Three meanings of j
The implementation distinguishes:
- `j` as a compiled chart/index whose cached inverse may stop gluing;
- `j` as the modular invariant, requiring the automorphic/elliptic gates;
- `j` as a representation or spin label.
In the chart lane, `j+1` is the available successor/rechart operation. It is not
a proof that overflow occurred and is not automatically the modular operation
`j ↦ j+1`.
## Added modules
- `DASHI.Foundations.Base12369RoleHierarchy`
- `DASHI.Foundations.MixedPrimeResolution`
- `DASHI.Foundations.Moonshine196883Boundary`
- `DASHI.Foundations.JChartSuccessorBoundary`
- `DASHI.Foundations.Base12369SuccessorRegression`
