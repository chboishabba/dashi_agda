# DASHI production DNA codec tranche

## Status

This tranche extends the theorem-bearing reference channel with a finite bounded
constraint policy and an executable adaptive codec. It is still a reference
implementation, not a validated wet-lab synthesis profile.

## Finite constraint state

`DASHI.Codec.DNAProductionConstraints` records:

- homopolymer runs capped at three;
- GC debt in the bounded set `{-2,-1,0,+1,+2}`;
- a nine-base suffix;
- finite rejection of `GATC` and `CTAG`;
- a bounded reverse-complement detector with stem length three and loop length
  four.

Admissibility remains the proposition carried by the state machine. The Boolean
function is its executable decision surface, not a post-generation validator.

## Variable branching and completion

`DASHI.Codec.DNAProductionChoices` derives its legal alphabet by evaluating all
four bases against the constraint machine. Consequently branch arity is derived
and may range from zero to four. Rank and unrank operate over that derived list.

`Completion h s` is an exact horizon-indexed proof object: every transition in a
completion carries its legality witness. The Python implementation memoizes the
corresponding exhaustive completion count and uses it to avoid bounded dead
ends.

## Coding

`tools/dna_production_codec.py` contains two distinct coding lanes:

1. a sentinel-framed mixed-radix ANS-style map from payload bytes into legal
   state-dependent DNA choices and back;
2. a 32-bit arithmetic coder for the emitted rank stream, with E1/E2/E3
   renormalization and interval assertions on every step.

The payload frame records bit length and DNA symbol count. These are explicit
framing data and are not hidden in a claim of self-delimitation.

`DASHI.Codec.DNAProductionNormalization` formalizes the structurally decreasing
normalization loop and the additional receipt a numeric backend must provide:
reachable-state invariants and a sufficient normalization budget.

## Compressive macros

`DASHI.Codec.DNACompressiveMacros` no longer retains the source block. A line
macro stores three chemistry quotient coordinates and one complement-phase
parity. Voxel and cube macros similarly retain chemistry fields plus parity
summaries.

The module includes two unequal lines with the same summary. This is deliberate:
it proves that the map is a genuine quotient rather than an identity wrapper.
Exact reconstruction therefore requires a residual lane.

## Compact invariants

`DASHI.Codec.DNACompactInvariants` provides a four-symbol repetition code with a
proved minimum Hamming distance of three. This deterministic receipt is separate
from the empirical CRC-16 and truncated SHA-256 checks in the Python benchmark.

The benchmark reports the conventional `1/2^16` and `1/2^64` random-collision
bounds only under the stated uniform-syndrome or ideal-hash assumptions.

## Empirical receipt

The CI benchmark emits `dna-production-benchmark.json` with:

- exact payload/DNA roundtrip status;
- payload bits per base;
- arithmetic-coded bits per base;
- legal branch-arity histogram;
- GC-debt histogram;
- maximum homopolymer run;
- forbidden-motif and bounded-hairpin counts;
- normalization counts;
- completion-cache statistics;
- macro summary size comparison;
- sampled single-substitution detection;
- encode/decode throughput.

These values are environment-specific measurements and are not imported as
mathematical axioms.
