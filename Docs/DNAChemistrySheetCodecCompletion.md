# DNA chemistry sheet codec completion

This tranche continues the merged DNA quotient/sheet/codec work with five concrete additions.

## Non-degenerate coarse summaries

`NonDegenerateChemistrySheetTower` replaces unit-valued coarse slots with computed summaries at the declared 4/16/64/256 levels:

- GC load and reverse-complement-4 risk;
- complement-span and short-hairpin risk;
- signed transition and cross-channel energies;
- total chemistry energy and operational admissibility.

The tower reconstructs exactly because it retains the leaf signal. It is therefore a redundant exact analysis tower. A critically sampled orthogonal or biorthogonal refinement remains a separate theorem target.

## Sourced nearest-neighbour thermodynamics

`SantaLucia1998Thermodynamics` instantiates the ten unified Watson-Crick nearest-neighbour entries using signed fixed-point units:

- delta H in 0.1 kcal/mol;
- delta S in 0.1 cal/(mol K);
- delta G at 37 C in 0.01 kcal/mol.

Primary authority:

- John SantaLucia Jr., *PNAS* 95 (1998), 1460-1465;
- DOI `10.1073/pnas.95.4.1460`;
- PMID `9465037`;
- unified fit based on 108 oligonucleotide duplexes.

The G.T mismatch source receipt references Allawi and SantaLucia, *Biochemistry* 36 (1997), DOI `10.1021/bi962590c`, covering 39 directly measured and six literature sequences.

## Adaptive codec obligations

`ChemistryAdaptiveReferenceCodec` reuses the verified two-choice reference machine from `DASHI.Codec.DNAConcreteReference`.

One trit is packetized into two legal binary branch choices, with `11` reserved as escape. The module proves:

- generability in the reference chemistry machine;
- ternary packet round-trip;
- exact two-base payload length;
- checksum preservation;
- recovery through the identity/no-error physical channel.

Full motif/hairpin admissibility and noisy substitution/indel/dropout recovery remain explicit production-promotion fields rather than being inferred from the reference channel.

## Published assay receipts

`PublishedChemistryAssayReceipts` records external aggregate authority for:

- SantaLucia unified thermodynamics;
- Allawi/SantaLucia mismatch thermodynamics;
- DNA Fountain perfect-recovery reporting (`10.1126/science.aaj2038`);
- DNA-Aeon constraint/error-correction in-vitro reporting (`10.1038/s41467-023-36297-3`).

These are real literature receipts. The repository does not claim a sequence-level DASHI quotient sufficiency reanalysis because the raw assay rows are not vendored.

## Ternary distortion and tetration

`FixedPointTernaryAndTetration` proves:

- an exact fixed-point ternary quantizer whose declared residual distortion is at most one unit;
- exact reconstruction of ternary representatives;
- the finite tetration recurrence `T(b,h+1) = b ^ T(b,h)`;
- `T(4,2) = 256` under the module's height-zero convention;
- a finite context-code carrier `Fin (T(b,h))`.

This proves the cardinal recurrence for transform-context codes. It does not identify the physical DNA carrier with that context tower. An analytic theorem over completed real coefficients and a semantics-preserving physical embedding remain separately typed promotion targets.
