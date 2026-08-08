# Monster 3B central-character inertia — Round 5

Round 5 separates the exact next representation-theoretic step from the exploratory nonary probe.

## Central-character inertia

The full normalizer may contain transformations that invert the central generator and exchange the two nontrivial central characters. The new generic construction distinguishes:

```text
CentralInertia  = transformations preserving z
CentralInverter = transformations inverting z.
```

For a literal central phase action, it proves:

```text
inertia:   W_zeta -> W_zeta
inverter:  W_zeta -> W_zetaSquared
inverter:  W_zetaSquared -> W_zeta.
```

The actual Monster phase-resolved sector remains a proof obligation. Its promotion record requires a two-sided equivalence between the chosen actual carrier and the literal zeta eigenspace.

## Promotion pipeline

`ActualZetaPromotionPipeline` combines exactly two inputs:

1. an actual phase-resolved zeta sector;
2. an `ActualZetaSectorRecognition` identifying that sector with the existing `729 x 90` Weyl model.

From those inputs, the code derives the internal inertia action, projector transport, multiplicity coordinates, and all existing Weyl relations without further compatibility premises.

## Twelve plus seventy-eight

The identity

```text
90 = 12 + 78
```

is retained only as dimension compatibility. A genuine theorem now requires:

```text
S_zeta ~= S_12 disjoint-union S_78
```

with two-sided inverse maps and block-diagonal inertia action. Character inner products and the actual intertwiner remain open.

## Nonary probe authority correction

The Ogg-prime map

```text
p |-> (floor(p/9), p mod 9)
```

is retained as a coordinate-valued probe. The code proves the complete finite address table and the following limits:

- every Ogg prime above 3 lies in a unit residue modulo 9;
- complement pairs are the ordinary additive-negation pairs `(1,8)`, `(2,7)`, `(4,5)`;
- the proposed ordered FRACTRAN map is not one uniform `+3` transform because `7+3 mod 9 = 1`, not `2`;
- `11+71 = 23+59 = 41+41 = 82`, so 41 is an arithmetic reflection fixed point.

None of these facts is promoted to a Monster duality, genus-zero theorem, invariant filtration, Leray projector, or explanation of the Ogg-prime list. An explicit `NonaryProbeEquivariantPromotion` record states what an actual upstairs operation would have to prove.

## Sources

- R. W. Barraclough and R. A. Wilson, *The Character Table of a Maximal Subgroup of the Monster*, DOI `10.1112/S1461157000001352`.
- John F. R. Duncan and Ken Ono, *The Jack Daniels Problem*, DOI `10.1016/j.jnt.2015.06.001`.
- John H. Conway and Simon P. Norton, *Monstrous Moonshine*, DOI `10.1112/blms/11.3.308`.
- Jean-Pierre Serre, *Linear Representations of Finite Groups*, DOI `10.1007/978-1-4684-9458-7`.
- I. M. Isaacs, *Character Theory of Finite Groups*, ISBN `978-0-486-68014-9`; no DOI assigned.

## Validation

```bash
bash scripts/check_monster_3b_central_character_inertia_round5.sh
```

The checker cascades through Round 4, rejects trust escapes and holes, and runs the pinned Agda 2.9 checker on the cumulative validation and aggregate roots.
