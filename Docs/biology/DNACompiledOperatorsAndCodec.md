# DNA compiled operators and codec tranche

This tranche advances the DNA lane from receipt-only architecture toward constructive mathematics and executable diagnostics.

## Formal modules

- `DASHI.Geometry.DNAFourAdicUltrametric`
  proves identity, symmetry, separation, and the strong triangle inequality for fixed-depth CAGT prefix addresses, then instantiates the repository `Ultrametric` record.
- `DASHI.Geometry.DNAFourWayLiftOperators`
  defines concrete four-way projection, broadcast, residual, reconstruction, complement equivariance, and reverse-complement involution.
- `DASHI.Biology.DNAChemistryFeatureQuotient`
  defines exact feature-fibre and basin quotients and proves reflexivity, symmetry, and transitivity. It deliberately does not promote an epsilon-proximity relation without a transitivity theorem.
- `DASHI.Biology.DNAChemistryEnergyAlgebra`
  gives exact codec and operational thermodynamic terms a concrete natural-number codomain and weighted additive Hamiltonian.
- `DASHI.Biology.DNACrossRankInteraction`
  separates ordered stacking, convolution, reverse-complement correlation, tensor contraction, quotient aggregation, and nonlinear gated composition.
- `DASHI.Foundations.DNATetrationalClosure`
  defines `tower 0 = 4` and `tower (suc n) = 4 ^ tower n`, while keeping tensor rank, support size, configuration count, and recursive closure depth distinct.
- `DASHI.Biology.DNACompiledOperatorsRegression`
  imports the tranche and checks representative constructive witnesses.

## Executable scripts

### Sheet-energy and chemistry observable generation

```bash
python scripts/gen_dna_chemistry_E_seq.py \
  --fasta data/genome.fa \
  --window 256 \
  --step 64 \
  --levels 4 \
  --cross-rank \
  --out outputs/dna_E_seq.npy
```

The generated energy matrix uses the exact UV chart, four-way coarse/detail lifts, and quadratic detail energies. Operational chemistry proxies are written separately to JSON.

### Variable-arity admissible codec

```bash
python scripts/dna_admissible_stream_codec.py encode \
  --digits payload_digits.json \
  --forbidden AAAA CCCC GGGG TTTT \
  --out encoded.json
```

The payload digits are mixed-radix choice indices. At each step the radix is exactly the number of admissible bases. Ternary is used only when this number is three.

Decoding recomputes the same admissible fibre and recovers the choice digits:

```bash
python scripts/dna_admissible_stream_codec.py decode \
  --sequence ACGT... \
  --out decoded.json
```

### Representation calibration

```bash
python scripts/compare_dna_chemistry_representations.py \
  --dataset measured_chemistry_features.npz \
  --out outputs/representation_comparison.json
```

The NPZ must supply externally grounded labels and the five documented representation matrices. The repository does not fabricate nearest-neighbour parameters, synthesis outcomes, or secondary-structure labels.

## Authority boundary

- CAGT, complement, reverse-complement, UV bijection, exact string constraints, and the finite prefix ultrametric are formal objects.
- Table-based nearest-neighbour, hairpin, dimer, salt, and temperature scores are exact evaluations relative to a supplied operational model.
- Agreement of those operational scores with microscopic molecular chemistry is empirical.
- Tetration does not by itself provide Conway surreal numbers; no surreal-number theorem is promoted here.
