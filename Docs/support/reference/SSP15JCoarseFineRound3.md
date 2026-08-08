# SSP15 nonary complement quotient and j-coarse/j-fine bridge

This tranche replaces the ambiguous slogan `10 / phase = 5` by an explicit finite quotient and gives every Ogg prime lane a distinct nonary coarse/fine address.

## Ten states as five complement modes with binary phase

The completed nonary carrier is the repository's existing

```text
T^2 disjoint-union {j}
```

with nine ordinary balanced-pair channels and one distinguished completion channel. It is encoded as

```text
{0,j}, {1,8}, {2,7}, {3,6}, {4,5}
```

together with a direct/counter phase. Encoding and decoding are two-sided inverses. Complement preserves the five-mode class and flips binary phase. The decimal carrier is also proved isomorphic to the existing `CoarseChannel` type, so this is not a duplicate ten-state enumeration.

## Internal five-by-three SSP15 carrier

The internal symmetry-phase carrier is

```text
ComplementMode5 x BalancedTrit
```

and its exhaustive list has fifteen entries. The five modes are put in an explicit finite bijection with the repository's five D4 irrep names. That bijection is only an indexing equivalence: the implementation does not claim that the complement mythology and D4 representation semantics have been proved identical.

Each internal lane has an exact characteristic projector coefficient in `{0,1}`. Own-lane projectors equal one, explicitly different lanes vanish, and coefficients are idempotent. Balanced phase reversal is involutive and transports the entire projector family equivariantly.

## Every Ogg prime receives an exact nonary address

For every established Monster/Ogg lane `p`, the code constructs

```text
p = 9 q + r
```

and records `q`, the ordinary fine digit `r`, its complement mode, and binary orientation. The complete table is:

```text
2  = 0*9 + 2
3  = 0*9 + 3
5  = 0*9 + 5
7  = 0*9 + 7
11 = 1*9 + 2
13 = 1*9 + 4
17 = 1*9 + 8
19 = 2*9 + 1
23 = 2*9 + 5
29 = 3*9 + 2
31 = 3*9 + 4
41 = 4*9 + 5
47 = 5*9 + 2
59 = 6*9 + 5
71 = 7*9 + 8.
```

All lanes except `p=3` are proved, by exhaustive typing, to occupy the three phase-mobile unit pairs `{1,8}`, `{2,7}`, and `{4,5}`. The `p=3` lane is the exceptional direct triadic-closure mode `{3,6}`.

The legacy Stage-5 observer remains for compatibility, but the canonical bridge now adds each lane's nonary address and observer kind. The rich spectrum proves, for example, that `p=2` and `p=71` retain the same local Stage-5 pattern while having distinct fine remainders `2` and `8`.

## Pointed-sign and depth-two identities

The pointed-sign carrier constructor is literal:

```text
1_star disjoint-union (X x C2).
```

The Ogg-value edges are proved exactly:

```text
2 -> 5 -> 11 -> 23 -> 47,
3 -> 7,
29 -> 59,
```

where every target is `2*source + 1`.

The depth-two ledger proves:

```text
2*5  = 9 + 1,
2*41 = 81 + 1,
41 + 40 = 81,
47 + 34 = 81,
59 + 22 = 81,
71 + 10 = 81,
71 + 5*2 = 81.
```

The last identity gives the refined `71` interpretation: it is the depth-two nonary remainder after the complete binary-phase presentation of the five first-order modes is removed. No invariant `71`-submodule is inferred from cardinal arithmetic.

## Concrete j-coarse/j-fine evaluation

The existing finite carrier has

```text
jCoarse = 9,
jFine = 3^9 = 19683,
jAbsolute = 3^11 = 177147,
jAbsolute = jCoarse * jFine.
```

A full fine assignment is a function from every coarse channel to `Fin 19683`. Evaluation at `completionJ` is supplied with the constant-assignment section, proving that every fine value occurs at `j`. The fibre over every chosen value is therefore inhabited.

The code corrects a subtle earlier overstatement: the codomain of evaluation has `3^9` values, but the set of complete assignments evaluating to one fixed value is not claimed to have cardinality `3^9`.

The authentic modular analogy is the forgetful map from elliptic curves with level structure to the coarse `j`-invariant. The finite DASHI evaluation model is not declared to be a modular curve, and it does not internally reprove the supersingular-`j` theorem.

## Prime-specific integration

`PrimeSpecificSSP15Reading p` now combines:

```text
exact nonary address,
complement mode and binary orientation,
nine-observer atlas entry,
9 x 3^9 coarse/fine scales,
concrete j-evaluation map.
```

This supersedes treating every prime as the same Stage-5 observation. The internal five-by-three carrier and the fifteen Ogg primes remain separate fifteen-element sets until an actual bijection with two-sided inverse laws is supplied.

## Prime-valued symmetry-phase fibres

`PrimeValuedSSP15State p` makes the final type separation explicit:

```text
Ogg prime valuation
x internal five-by-three lane
x residual geometry.
```

Every Ogg prime indexes a full fibre of internal symmetry-phase choices. Phase reversal acts inside the fibre and leaves the prime valuation unchanged. This realizes structured examples such as

```text
(71, A1, neutral, binary-five-interface residual)
(71, A2, counterposed, binary-five-interface residual)
```

as distinct typed values with the same `p=71` valuation. Equal cardinalities of the Ogg set and the internal lane set still do not manufacture a canonical bijection.

## Sources

- Nicholas M. Katz and Barry Mazur, *Arithmetic Moduli of Elliptic Curves*, DOI `10.1515/9781400881710`.
- John F. R. Duncan and Ken Ono, *The Jack Daniels Problem*, DOI `10.1016/j.jnt.2015.06.001`.
- Jean-Pierre Serre, *Linear Representations of Finite Groups*, DOI `10.1007/978-1-4684-9458-7`.
- Audrey Terras, *Fourier Analysis on Finite Groups and Applications*, DOI `10.1017/CBO9780511626265`.
- Thomas Breuer, *The GAP Character Table Library*, Version 1.3.11; no DOI assigned.
- Alexander Hulpke, GAP Transitive Groups Library degree-nine data; no DOI assigned.
- Conway, Curtis, Norton, Parker and Wilson, *Atlas of Finite Groups*, ISBN `978-0-19-853199-9`; no DOI assigned.

## Validation

```bash
bash scripts/check_ssp15_j_coarse_fine_round3.sh
```

The checker invokes the repository's pinned Agda 2.9 runner and cannot silently succeed when Agda is missing.
