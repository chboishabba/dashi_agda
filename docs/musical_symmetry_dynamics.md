# Musical symmetry as a repair fixed class

## Source and scope

This tranche is motivated by *Algebraic Applications in Investigation of Musical Symmetry* (Springer Proceedings in Mathematics & Statistics, 2025; DOI `10.1007/978-3-031-84869-8_5`). The source chapter supplies the algebraic side of the comparison: musical objects are acted on by transformations, and symmetric objects are identified through invariance or fixed-class structure.

DASHI adds a deliberately narrower dynamical question:

> Given an algebraic symmetry class, can a typed repair operator have exactly that class as its fixed points, and can its finite basins be computed without promoting a cognitive explanation?

The implementation answers **yes** to the structural question and **not yet** to the cognitive question.

## Formal split

`DASHI.Music.MusicalSymmetryDynamicsCore` defines:

- an involutive symmetry operator `symmetry`,
- the fixed-class predicate `Symmetric`,
- an asymmetry-energy carrier whose zero set is exactly the fixed class,
- a repair operator that lands in the fixed class, fixes every symmetric state, and does not increase the supplied defect energy,
- a proof that repair is idempotent,
- a proof that repair fixed points are exactly symmetric states,
- a separate basin-assignment and finite-volume surface.

The separation matters. Fixed-point structure does **not** imply that human listeners prefer the corresponding melodies, nor that symmetric states have larger basins under an independently derived cognitive process.

## Exact finite witness

`DASHI.Music.BooleanMelodySymmetryWitness` supplies a complete four-state model:

```text
states:   00, 01, 10, 11
symmetry: swap the two positions
repair:   copy the left position to the right
```

The exact facts are:

```text
fixed/symmetric states: 00 and 11
01 -> 00
10 -> 11
repair is idempotent
repair energy is zero after one step
basin(00) = 2
basin(11) = 2
all four states are accounted for
```

This establishes a genuine dynamical extension of algebraic symmetry, but the result is mechanism-relative: the repair was defined to land in the symmetric class.

## Replacement for the earlier beta-weighted toy

The earlier exploratory Python model used a score of the form

```text
distance + beta * asymmetry_energy
```

and therefore built the desired result directly into the assignment rule. It showed that rewarding symmetry rewards symmetry; it did not establish an independent explanation.

`scripts/musical_symmetry_basin_diagnostic.py` replaces that diagnostic with three lanes:

1. **Geometric null** — nearest-prototype assignment with no symmetry or compression prior.
2. **Compression hypothesis** — symmetric reverse-inversion prototypes receive a shorter grammar code: half-sequence plus an inversion axis, versus a full sequence for generic prototypes.
3. **Shuffled-code control** — the same short and long code lengths are randomly reassigned among prototypes.

The script uses pitch-class sequences in `(Z/12Z)^n` modulo global transposition. Reverse-inversion defect is minimized over all twelve T/I axes. It reports basin shares over repeated Monte Carlo trials and can emit a self-contained SVG.

Run:

```bash
python scripts/musical_symmetry_basin_diagnostic.py \
  --samples 2000 \
  --trials 12 \
  --compression-weight 1.0 \
  --output-json musical-symmetry-report.json \
  --output-svg musical-symmetry-report.svg

python -m unittest discover \
  -s scripts/tests \
  -p 'test_musical_symmetry_basin_diagnostic.py' \
  -v
```

## Claim boundary

`DASHI.Music.MusicalSymmetryCognitiveBoundary` separates two gates.

The structural gate is closed by the exact finite witness:

- involutive symmetry specified,
- zero-defect fixed class proved,
- repair/fixed-point equivalence proved,
- finite basin partition computed.

The cognitive gate remains open. Promotion would require at least:

- no direct reward of the target symmetry functional,
- a mechanism derived from an independent principle such as a validated compression model,
- defeat of geometric and shuffled-prior controls,
- held-out corpus replication,
- correlation with human perception or behaviour,
- robustness to pitch representation and quantisation choices.

Accordingly:

```text
algebraic dynamical extension: proved in the finite witness
compression explanation: candidate-only
human cognitive explanation: not promoted
```

## What is potentially new

The source algebra classifies musical symmetry. This tranche adds a reusable typed bridge from:

```text
group/involution fixed class
    -> zero-defect class
    -> idempotent repair dynamics
    -> exact finite basin partition
```

That bridge is mathematically useful. A publishable cognitive claim would begin only when the repair or prior is independently motivated and the resulting basin advantage survives the stated controls and behavioural validation.
