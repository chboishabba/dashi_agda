# Monster 3B central-character inertia — Round 5

Round 5 separates the exact next representation-theoretic step from the now fully formalized nonary/Ogg arithmetic probe.

## Central-character inertia

The full normalizer may contain transformations that invert the central generator and exchange the two nontrivial central characters. The generic construction distinguishes:

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

## Complete nonary address theorem

`MonsterOggNonaryProbeAuthorityExact.agda` computes the full Euclidean table

```text
p = 9 q + r
```

for all fifteen Ogg primes:

```text
2  = 0*9 + 2      3  = 0*9 + 3      5  = 0*9 + 5
7  = 0*9 + 7      11 = 1*9 + 2      13 = 1*9 + 4
17 = 1*9 + 8      19 = 2*9 + 1      23 = 2*9 + 5
29 = 3*9 + 2      31 = 3*9 + 4      41 = 4*9 + 5
47 = 5*9 + 2      59 = 6*9 + 5      71 = 7*9 + 8.
```

The finite carrier proves constructively that no fine residue is `0` or `6`. This is stronger than a Boolean table audit: every lane produces an inhabitant of the indexed type

```text
OpenNonaryResidue r
```

whose only constructors are at `1,2,3,4,5,7,8`; elimination proves both exclusions.

No transition relation is constructed. Therefore “open residue” means only exclusion of the two proposed arithmetic endpoints. It does not by itself prove that a lane has a dynamical forward move.

## Complement modes and orientations

Every Ogg prime above three has one of the six unit residues

```text
1, 2, 4, 5, 7, 8 mod 9.
```

The complement operation is exact additive negation:

```text
1 <-> 8
2 <-> 7
4 <-> 5,
```

and the code proves both

```text
r + complement(r) = 9
complement(complement(r)) = r.
```

It then factors the six units into

```text
UnitComplementMode x UnitOrientation
```

with three modes `18`, `27`, `45` and two orientations `direct`, `counter`. Complement preserves the mode and reverses the orientation. This is the precise finite content behind the statement that `r` and `9-r` are two orientations of the same complement choice.

## Sorted residue signature versus actual FRACTRAN replacements

The supplied sorted comparison is retained exactly:

```text
start residues = [7,2,5]
end residues   = [2,5,8].
```

Its second and third entries satisfy `+3 mod 9`, but its first does not:

```text
2 + 3 = 5 mod 9
5 + 3 = 8 mod 9
7 + 3 = 1 mod 9, not 2.
```

Consequently the proposed ordered FRACTRAN map is not one uniform `+3` transform.

More importantly, sorted zipping is not the actual FRACTRAN replacement relation. The repository’s exact earning program fires the fractions

```text
47/23, 59/7, 71/11,
```

so the true replacement graph is

```text
23 -> 47      residues 5 -> 2
7  -> 59      residues 7 -> 5
11 -> 71      residues 2 -> 8.
```

None of these three actual replacement legs is `+3 mod 9`. The module imports the existing `MoonshineEarn` proof and exposes the exact computation

```text
1771 / 23 * 47 = 3619
3619 / 7  * 59 = 30503
30503 / 11 * 71 = 196883
47 * 59 * 71 = 196883
47 * 59 * 71 + 1 = 196884.
```

This is a real FRACTRAN execution theorem, not a residue analogy.

## Depth-two nonary arithmetic

The exact depth-two identities are:

```text
71 + 10 = 81
2 * 41 = 81 + 1
11 + 71 = 82
23 + 59 = 82
41 + 41 = 82.
```

Thus `41` is the fixed point of the finite reflection `p |-> 82-p`. The code does not turn that reflection into a Leray projection: no vector space, inner product, divergence-free subspace, or idempotent operator has been constructed from it.

## The 7A normalization offset

There are two closely related `7A` series conventions that must not be conflated.

For the unnormalised eta-quotient representative

```text
(h + 7)^2 / h,
```

where `h = (eta(tau)/eta(7 tau))^4`, the prefix is represented as

```text
q^-1 + 10 + 51 q + 204 q^2 + ... .
```

The normalized McKay–Thompson Hauptmodul subtracts the constant ten:

```text
T_7A = q^-1 + 51 q + 204 q^2 + ... .
```

Accordingly, the unnormalised representative has constant `10`, while the normalized `7A` Hauptmodul has constant `0`. The formalized relation is

```text
normalizedConstant + 10 = unnormalizedConstant.
```

The two exact arithmetic coincidences retained by validation are

```text
71 + 10 = 81
196874 + 10 = 196884.
```

Equivalently, validation substitutes the unnormalised `7A` constant into both identities. Neither equality identifies the normalization offset with a ten-dimensional surviving Monster subspace. Such an interpretation would require an actual graded carrier and trace or dimension map realizing the ten.

## Exact semantic 7+7+1 carrier equivalence

The existing semantic partition is reconstructed directly as finite lane types:

```text
MirrorA7 = [2,3,5,7,11,13,17]
MirrorB7 = [19,23,29,31,41,47,59]
Sign1    = [71].
```

The address authority proves the three counts `7`, `7`, and `1`, and their sum `15`. The separate module `MonsterOggNonarySevenSevenOneEquivalenceExact.agda` upgrades that arithmetic to a two-sided finite equivalence

```text
MonsterPrimeLane
  ~= MirrorA7Lane disjoint-union (MirrorB7Lane disjoint-union Sign1Lane).
```

It constructs classification and forgetting maps and proves both round trips by exhaustive pattern matching. Thus no lane is omitted or duplicated by the semantic partition.

Every MirrorA and MirrorB lane lies in a coarse sheet `0` through `6`, while `p71` has address

```text
71 = 7*9 + 8.
```

The uniqueness theorem proves that any Ogg lane whose coarse sheet equals `7` is propositionally equal to `p71`. This makes the finite carrier organization geometrically explicit. It does not prove that the two septets are invariant Monster modules, literal CM split/inert classes, or positive frame factors.

## Genus-zero and Clay boundary

The nonary table is a static finite coordinate system. The following implications remain explicitly false on this branch:

```text
nonary address -> actual forward dynamics
nonary address -> equivariant Monster operation
absence of residues 0 and 6 -> genus-zero
nonary cascade acyclicity <-> genus-zero
41 reflection -> Leray projector
7+7+1 finite equivalence -> Monster-module direct sum
unnormalised 7A offset ten -> ten-dimensional Monster mass
nonary arithmetic -> Yang--Mills Clay theorem.
```

A genus-zero argument would need a modular group, a compactified quotient curve, and a proof of genus zero or Hauptmodul uniqueness. A Clay argument would still need the analytic constructive-QFT package: reflection positivity, continuum limit, Wightman/Osterwalder–Schrader reconstruction, and a dimensionful Hamiltonian spectral gap.

## Sources

- R. W. Barraclough and R. A. Wilson, *The Character Table of a Maximal Subgroup of the Monster*, DOI `10.1112/S1461157000001352`.
- John F. R. Duncan and Ken Ono, *The Jack Daniels Problem*, DOI `10.1016/j.jnt.2015.06.001`.
- John H. Conway and Simon P. Norton, *Monstrous Moonshine*, DOI `10.1112/blms/11.3.308`.
- David Ford, John McKay and Simon P. Norton, *More on Replicable Functions*, DOI `10.1080/00927879408825127`.
- John McKay and Heiko Strauss, *The q-series of monstrous moonshine and the decomposition of the head characters*, DOI `10.1080/00927879008823911`.
- John H. Conway, *FRACTRAN: A Simple Universal Programming Language for Arithmetic*, 1987; no DOI asserted.
- Jean-Pierre Serre, *Linear Representations of Finite Groups*, DOI `10.1007/978-1-4684-9458-7`.
- I. M. Isaacs, *Character Theory of Finite Groups*, ISBN `978-0-486-68014-9`; no DOI assigned.

## Validation

```bash
bash scripts/check_monster_3b_central_character_inertia_round5.sh
```

The checker cascades through Round 4, rejects trust escapes and holes, requires every positive and negative theorem named above, and runs the pinned Agda 2.9 checker on the cumulative validation and aggregate roots.
