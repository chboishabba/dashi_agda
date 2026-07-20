# DNA-first DASHI codec formalism

## Status

This tranche is a typed specification and executable algebraic core. It does **not** claim a completed biochemical DNA-storage implementation, a proved coding-capacity optimum for a chosen chemistry model, or a proved probabilistic CRC-equivalence theorem.

The canonical modules are:

- `DASHI.Codec.BalancedTritBitFibre`
- `DASHI.Codec.DNAFirstFormalism`
- `DASHI.Codec.DNAFirstFormalismRegression`

## Existing spine reused

The implementation deliberately reuses `DASHI.Algebra.Trit` rather than introducing another ternary carrier. Its `neg`, `zer`, `pos`, and `inv` objects remain canonical. This is compatible with `DASHI.Foundations.SSPTritCarrier`, which already bridges the same carrier into `SSPTrit` and `Base369.TriTruth`.

## Exact bit ↔ balanced-trit factorisation

`BalancedTritBitFibre` formalises the exact support/sign decomposition:

- zero has an inactive support bit and no sign bit;
- positive and negative trits have an active support bit and one sign bit;
- decoding and encoding are mutually inverse;
- ternary involution fixes zero and flips only the sign fibre;
- a word of length `n` with `k` non-zero trits emits exactly `n + k` bits.

This is a structural binary carrier for balanced ternary, not a claim that ternary is primitively binary. The module intentionally proves the exact finite-word cost law and leaves distribution-dependent average-rate statements outside the theorem surface.

## DNA carrier and generability

`DNAFirstFormalism` introduces the CAGT carrier, complement involution, reverse complement, and the 3/9/27 geometry:

- `Line3`
- `Voxel9`
- `SixSheet`
- `Cube27`

Validity is defined by `Generable`: a sequence is valid exactly when there is a typed `Trace` through a `ConstraintMachine`, with an admissibility witness for every emitted base.

The operational state is factored into suffix, GC-debt, bounded hairpin-guard, lift-phase, and orbit-phase components. Concrete chemistry policies remain parameters so that the formal generability layer is not confused with one empirical choice of thresholds.

## Six-sheet completion

`CompletionViability.Viable` is exact existential completion:

> a partial object is viable when there exists a complete extension satisfying the completion predicate.

A bounded-lookahead or cached implementation may later prove soundness into this exact surface. It must not silently redefine viability.

## Recognisable lifts, eigenstates, and invariants

`LiftTower` records line, voxel, and cube macro-alphabets, their lift maps, recognisability obligations, and macro-admissibility relations.

`EigenResidualSystem` requires eigenstates to carry a dynamical fixed-point witness and requires representative and residual maps to commute with involution. This prevents “eigenstate” from degrading into an unproved codebook metaphor.

`MultiscaleInvariantFamily` models mirrored group-valued or signed checks. It deliberately does not append a binary CRC primitive.

## Streaming capacity boundary

`StreamingChoiceSurface` exposes the legal state-dependent branch count and a coder selection surface. It records the object needed by arithmetic coding or ANS without assigning a fixed trit or bit budget to a 27-base cube.

A future concrete tranche should instantiate:

1. a finite suffix/motif automaton;
2. bounded GC debt;
3. bounded reverse-complement hairpin guards;
4. a concrete scan order;
5. recognisable line/voxel/cube lifts;
6. a sound completion cache;
7. an invertible arithmetic/ANS coder;
8. quantitative rate and error-detection receipts.
