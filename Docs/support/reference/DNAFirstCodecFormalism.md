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
DASHI/Codec/DNAConcreteValidation.agda
The aggregate module imports the abstract spine, concrete channel, lift tower, MDL/invariant layer, and all fibre bridges.
## Remaining production work
1. Replace the alternating-pair baseline with a decidable finite machine for realistic motif, homopolymer, GC-debt, and hairpin constraints.
2. Derive ordered legal-base vectors and finite ranks for variable branch arities 1–4.
3. Implement a true arithmetic/range or rANS backend with terminal-state and framing proofs.
4. Generalise the completion cache to bounded horizons and prove soundness, plus completeness within the stated horizon.
5. Replace identity macro-symbols with smaller canonical eigen-representatives and exact residual reconstruction.
6. Add compact multiscale checks with explicit substitution, indel, reverse-complement, and boundary-misalignment guarantees.
7. Add executable benchmarks for rate, throughput, branch distribution, chemistry statistics, cache effectiveness, and lift benefit.
This tranche is a typed specification and executable algebraic core. It does **not** claim a completed biochemical DNA-storage implementation, a proved coding-capacity optimum for a chosen chemistry model, or a proved probabilistic CRC-equivalence theorem.
The canonical modules are:
- `DASHI.Codec.DNAFirstFormalismRegression`
## Existing spine reused
The implementation deliberately reuses `DASHI.Algebra.Trit` rather than introducing another ternary carrier. Its `neg`, `zer`, `pos`, and `inv` objects remain canonical. `DASHI.Interop.CodecCarrierFibreBridge` connects the resulting support/sign fibre directly to `DASHI.Foundations.SSPTritCarrier`, which already bridges that carrier into `SSPTrit` and `Base369.TriTruth`.
The two-point sign fibre is also identified with the existing `OrientationPolarity` used by `DASHI.Foundations.HexTruthPolarityFactor`. Sign inversion commutes with the existing polarity flip. This reuses the repository's established `HexTruth ≅ TriTruth × Polarity` orientation fibre without claiming that a three-state trit is itself a six-state `HexTruth` object.
`BalancedTritBitFibre` formalises the exact support/sign decomposition:
- positive and negative trits have an active support bit and one sign bit;
- decoding and encoding are mutually inverse;
- ternary involution fixes zero and flips only the sign fibre;
- a word of length `n` with `k` non-zero trits emits exactly `n + k` bits.
This is a structural binary carrier for balanced ternary, not a claim that ternary is primitively binary. The module intentionally proves the exact finite-word cost law and leaves distribution-dependent average-rate statements outside the theorem surface.
## DNA quotient/fibre factorisation
`DNACarrierFibre` gives the four-base carrier an exact chemistry/orbit presentation:
- `ChemicalPair` distinguishes the A/T and C/G complement orbits;
- `ComplementPhase` identifies the member within each orbit;
- complement preserves the chemical pair and flips only complement phase.
This is the DNA analogue of quotient-plus-fibre structure. It is not a claim that DNA bases are primitively two bits. The chemistry quotient can feed GC-debt and admissibility logic, while the complement phase remains available to reverse-complement, mirror, eigen-orbit, and invariant surfaces.
The analogy with balanced ternary is structural rather than cardinal:
| carrier | quotient/base coordinate | involutive fibre |
|---|---|---|
| balanced trit | zero versus non-zero support | positive versus negative sign |
| DNA base | A/T versus C/G chemical pair | member of the complement orbit |
| Base369 `HexTruth` | `TriTruth` phase | orientation polarity |
These presentations share the rule that the involution acts in the fibre while preserving the quotient coordinate. They are not identified as the same carrier.
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
## Cross-pollination boundaries
The shared quotient/fibre grammar can now be consumed by codec, Base369, SSP, p-adic-address, and multiscale-invariant lanes. Safe reuse means transporting typed involution, roundtrip, and equivariance laws. It does **not** mean that chemistry classes, support masks, p-adic digits, `TriTruth`, and physical observables become interchangeable.
In particular:
- DNA complement phase may feed mirrored invariants, but does not by itself define a balanced-trit residual;
- SSP trits may use the exact bit fibre, but this does not prove a source distribution or compression ratio;
- Base369 polarity supplies the canonical two-point orientation fibre, but no direct `TritFibre ≅ HexTruth` claim is made;
- recognisable lifts may carry these fibres across scale only after concrete recognisability and equivariance witnesses are supplied.
A future concrete tranche should instantiate:
1. a finite suffix/motif automaton;
2. bounded GC debt;
3. bounded reverse-complement hairpin guards;
4. a concrete scan order;
5. recognisable line/voxel/cube lifts;
6. a sound completion cache;
7. an invertible arithmetic/ANS coder;
8. quotient/fibre equivariance through concrete lift maps;
9. quantitative rate and error-detection receipts.
