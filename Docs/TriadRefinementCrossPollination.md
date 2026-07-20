# Triad refinement cross-pollination

This note records the additional bridges attached to the current saturated Hecke
refinement lane.

## 1. MDL-governed promotion

`Ontology/Hecke/DirectedCorrelationMDLPromotion.agda` turns the invariant ladder
into a promotion problem rather than an unrestricted feature-expansion problem:

1. flat histogram,
2. ordered triad histogram,
3. symmetric sector correlation,
4. directed 3×3 sector interaction.

A richer level is admissible only when:

- the preceding level is exhausted on the relevant current scope,
- the target carries a pair-specific separation obligation,
- the target's total model-plus-residual description length is no worse.

The fixed structural costs are bookkeeping defaults for the current finite
carrier. They are not claimed to be an optimal universal code. This imports the
existing MDL/ZKP discipline into the Hecke lane: heuristics may propose richer
summaries, but promotion must be receipt-bearing and pay for complexity.

## 2. Triad × five-class SSP carrier

`Ontology/Hecke/TriadFiveSSPCoordinateBridge.agda` makes the candidate

```text
15 = 3 × 5
```

surface fully explicit. It defines:

- three existing triadic sectors,
- five local symmetry-class slots,
- fifteen row-major coordinates,
- an explicit reversible labeling by the existing fifteen-element `SSP` carrier.

The two round-trip proofs establish a finite carrier equivalence for that chosen
labeling. They do **not** establish:

- a canonical Monster action,
- a Monster representation,
- moonshine compatibility,
- a physical interpretation of the ordering,
- or that the five classes are the actual orbit quotient discovered by the
  long-compute histogram lane.

Those stronger claims are collected in `MonsterInterpretationObligation`; the
record deliberately has no inhabitant in this module.

## 3. Correct Monster → SSP15 → FRACTRAN hierarchy

`DASHI/Combinatorics/MonsterSSPFractranProjection.agda` records the stronger and
more faithful interpretation:

```text
Monster-side object / representation / orbit data
  -> project to multiplicities on the fifteen supersingular primes
  -> SSP15 exponent state
  -> FRACTRAN execution over that selected prime basis
```

Thus SSP15 is the compressed Monster-facing basis, while FRACTRAN is the
prime-exponent transition language. The core state is:

```text
SSP15ExponentState = SSP -> Nat
```

A `MonsterSSPCompression` must identify exactly which Monster-side equivalence is
captured by equal SSP15 projections. A `MonsterSSPResidualCodec` adds the missing
non-SSP detail when exact reconstruction is required.

The actual dynamic bridge is a commuting-square obligation:

```text
project (monsterStep object)
  = fractranStep (project object)
```

This is packaged by `MonsterSSPFractranSimulation`. It is not derived merely from
the fact that both sides mention primes.

## 4. Relation to the existing EV5 FRACTRAN toy

`DASHI/Combinatorics/TriadFiveFractranIndex.agda` remains a useful finite adapter to
the repo's existing concrete `FractranCOL.EV5` machine. It should now be read as a
toy/indexing lane, not as the primary Monster compression theorem.

The primary structure is fifteen SSP prime lanes. The existing five-lane machine is
only one bounded executable fragment. Three EV5 banks can model a `3 × 5` table,
but this does not itself prove that the Monster projection factors into those three
banks.

## 5. Generic SSP15 quotient codec

`DASHI/Combinatorics/SSP15FractranCompression.agda` remains useful as a generic
codec contract. It separates:

1. an outcome-preserving quotient,
2. a lossless label-plus-residual codec,
3. a dynamics-preserving compressed transition.

However, an arbitrary `EV5 -> SSP` classifier is not the canonical Monster story.
For the Monster-facing lane, the encoder should arise by first projecting Monster
structure onto the fifteen SSP multiplicities and only then executing or compressing
that exponent state.

## 6. Combined flow

```text
computed Hecke sector data
  -> promoted invariant
  -> candidate Monster-side structural interpretation
  -> fifteen-SSP multiplicity projection
  -> SSP15 prime-exponent state
  -> FRACTRAN transition system
  -> optional residual outside SSP15
  -> outcome / transition / run receipts
```

The Monster-facing compression is therefore upstream of FRACTRAN execution, not a
post-hoc relabeling of arbitrary FRACTRAN states.

## 7. Immediate discharge order

1. Focus-check the MDL, triad-five, SSP projection, and FRACTRAN modules.
2. Specify the actual Monster-side carrier being compressed.
3. Define the fifteen SSP multiplicity/invariant projection.
4. Prove projection soundness and completeness for the declared Monster-side
   equivalence.
5. Define FRACTRAN instructions over `SSP15ExponentState`.
6. Prove the Monster step / FRACTRAN step commuting square.
7. Add a residual channel for structure outside the SSP projection when exact
   reconstruction is required.
8. Charge the model, projected state, transition program, and residual using MDL.
9. Only after those steps attempt a representation or moonshine interpretation.
