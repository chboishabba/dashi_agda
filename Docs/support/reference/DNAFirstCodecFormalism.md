# DNA-first DASHI codec formalism

## Status

The repository now contains both the abstract DNA-first specification and a small executable reference channel. The concrete channel is deliberately narrow: it proves an end-to-end bit → legal DNA → bit roundtrip, exact branch enumeration, a sound completion witness, concrete 3/9/27 lift plumbing, reconstructive eigen/residual selection, and injective invariants. It does **not** claim production biochemical constraints, capacity optimality, a completed arithmetic/rANS backend, or CRC-equivalent error correction.

The aggregate validation target is:

- `DASHI.Codec.DNAConcreteValidation`

## Canonical modules

- `DASHI.Codec.BalancedTritBitFibre`
- `DASHI.Codec.DNAFirstFormalism`
- `DASHI.Codec.DNACarrierFibre`
- `DASHI.Codec.DNAConcreteReference`
- `DASHI.Codec.DNAConcreteLiftTower`
- `DASHI.Codec.DNAEigenMDLInvariant`
- `DASHI.Foundations.InvolutiveFibrePresentation`
- `DASHI.Interop.CodecCarrierFibreBridge`
- `DASHI.Interop.CodecFibrePresentations`

## Exact bit ↔ balanced-trit factorisation

`BalancedTritBitFibre` proves the support/sign decomposition:

- zero has an inactive support bit and no sign bit;
- positive and negative trits have active support and one sign bit;
- encoding and decoding are mutually inverse;
- ternary involution fixes zero and flips only sign;
- a length-`n` word with `k` non-zero trits has raw structural cost `n + k` bits.

This is a structural binary presentation, not a statement that ternary is primitively binary or entropy-optimal without coding the two streams.

## Cross-carrier quotient/fibre law

`InvolutiveFibrePresentation` packages an exact encoded presentation, a coarser quotient, encode/decode roundtrips, and an involution that leaves the quotient fixed.

Concrete instances are supplied for:

1. balanced trits: zero/non-zero support plus optional sign;
2. DNA: A/T versus C/G chemistry plus complement phase;
3. `HexTruth`: `TriTruth` phase plus orientation polarity.

The instances formalise a shared commuting law without identifying the three carrier types.

## Concrete reference constrained channel

`DNAConcreteReference` alternates between two state fibres:

- `atTurn`: legal bases are `A` and `T`;
- `cgTurn`: legal bases are `C` and `G`.

Each state therefore has exactly two legal bases. A payload bit selects one by `unrank`; a legal base is recovered by `rank`. Both roundtrip laws are proved.

The resulting reference encoder has the theorem:

```text
decode (encode bits) ≡ bits
```

Every encoded word also carries a `Generable` trace through the abstract `ConstraintMachine` semantics. Because chemical fibres alternate, even-length outputs are exactly 50% GC and adjacent homopolymers are impossible.

This channel is a verified baseline, not a full synthesis model. It intentionally does not yet encode long forbidden motifs, realistic bounded GC debt, or general reverse-complement hairpin screening.

## Completion cache

The concrete channel exposes `cacheViable`. A positive answer yields an explicit legal next-base witness, so cache soundness is theorem-bearing rather than a heuristic redefinition of exact viability.

The current receipt is one-step. General horizon-indexed completion tables remain follow-on work.

## Concrete 3/9/27 lifts

`DNAConcreteLiftTower` instantiates line, voxel, and cube symbols. Each symbol retains:

- the exact source block;
- its pointwise chemical quotient summary.

Projection after lifting is definitionally exact, and complement invariance of the chemical quotient is proved at line, voxel, and cube scales.

This is an identity-recognisable baseline. It validates geometry, projection, and equivariance plumbing but is not yet a compressive macro-alphabet. A later tranche may replace exact source retention with canonical representatives plus reconstructive residuals.

## Eigenstate, residual, and MDL action

`DNAEigenMDLInvariant` chooses the primary member of each chemical pair as representative:

- `A` represents the A/T pair;
- `C` represents the C/G pair.

Complement phase is the residual. The pair reconstructs the exact nucleotide. Representatives are fixed points of the induced projection update, complement preserves the representative, and flips the residual.

A finite action assigns zero cost to the residual that reconstructs the observed base and one to the alternative. The selected residual is proved minimal. This is the smallest concrete MDL receipt; richer model length, context cost, and multiscale action terms remain open.

## Operational invariants

The exact `BaseFibre` encoding is injective, so it detects every changed nucleotide. Its list lift is also injective and detects every changed word.

This is deliberately described as an exact invariant, not a short checksum or CRC. Compact sketches require separate collision or distance bounds.

## CI validation

`.github/workflows/dna-concrete-codec.yml` installs Agda and the standard library, then typechecks:

```text
DASHI/Codec/DNAConcreteValidation.agda
```

The aggregate module imports the abstract spine, concrete channel, lift tower, MDL/invariant layer, and all fibre bridges.

## Remaining production work

1. Replace the alternating-pair baseline with a decidable finite machine for realistic motif, homopolymer, GC-debt, and hairpin constraints.
2. Derive ordered legal-base vectors and finite ranks for variable branch arities 1–4.
3. Implement a true arithmetic/range or rANS backend with terminal-state and framing proofs.
4. Generalise the completion cache to bounded horizons and prove soundness, plus completeness within the stated horizon.
5. Replace identity macro-symbols with smaller canonical eigen-representatives and exact residual reconstruction.
6. Add compact multiscale checks with explicit substitution, indel, reverse-complement, and boundary-misalignment guarantees.
7. Add executable benchmarks for rate, throughput, branch distribution, chemistry statistics, cache effectiveness, and lift benefit.
