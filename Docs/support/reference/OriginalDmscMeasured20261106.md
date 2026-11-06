# Original Shine–Dalgarno dmsC measured-data readout — 2026-11-06

## Provenance and scope

- Original study: Kuo et al., **Global fitness landscapes of the
  Shine-Dalgarno sequence**, *Genome Research* 30 (2020), 711–723,
  DOI `10.1101/gr.260182.119`.
- Reanalysis: Martí-Gómez et al., **Inference and visualization of complex
  genotype–phenotype maps**, *Molecular Biology and Evolution* (2026),
  DOI `10.1093/molbev/msag023`.
- Exact original data path, as checked by connected GitHub:
  `cmarti/shine_dalgarno/data/dmsc.csv`, Git blob
  `151cd87272cbdd6bcc2b1e70bdfd2a4ea2933d2c`.
- Original CSV columns:
  `Genotype,Fepb.1,Fepb.2,Fepb.3,Arti.1,Arti.2,Arti.3,dmsC.1,dmsC.2,dmsC.3`.
- Measured source material includes dmsC replicate observations, not just an
  inferred 4^9 model prediction. Each genotype's available original dmsC
  replicates are averaged to one **genotype-level** response before splitting.

**Execution standing:** These results were computed in this conversation
from the full original Git blob via a direct in-memory JavaScript readout.
The source Git blob identity is recorded, but *this is not an independent
Python/parallel_checker/Agda acceptance receipt*. A matching Python
reproduction recipe is committed as
`scripts/check_original_dmsc_holdout.py`.

## Source data census

| Item | Count |
|---|---:|
| All 9-mer genotypes in original source table | 262,144 |
| Genotypes with 0 observed dmsC replicates | 4,579 |
| With exactly 1 observed dmsC replicate | 32,030 |
| With exactly 2 observed dmsC replicates | 73,550 |
| With exactly 3 observed dmsC replicates | 151,985 |
| **Genotypes with at least one measured dmsC response** | **257,565** |
| Total observed dmsC replicate values | **635,085** |

## Out-of-genotype predictive test

All 257,565 originally observed genotype means were assigned with one
deterministic FNV-1a 32-bit hash of
`dashi-2026-v1:<nine-base-RNA-sequence>`:

| Partition | Measured genotypes |
|---|---:|
| Train (70% hash range) | 181,279 |
| Validation (15% range) | 37,784 |
| Held-out test (15% range) | 38,502 |

Ordinary least squares models fitted only on train genotype means. The
intercept-only, guanine-count, guanine/cytosine-count and
guanine/cytosine/uracil-count candidates were compared only on validation.

| Model | Validation RMSE |
|---|---:|
| Intercept only | 0.358985 |
| Intercept + G count | 0.341465 |
| Intercept + G + C | 0.320720 |
| **Intercept + G + C + U** | **0.316250** |

The selected G/C/U count regression (the published unit is log-fluorescence)
was:

```text
predicted_mean_dmsC =
  0.9184605379237479
+ 0.03201325770191533 * count_G
- 0.11796487694215801 * count_C
- 0.048654729055004516 * count_U
```

The **single held-out test readout** was:

| Held-out metric | Selected G/C/U model | Train-mean baseline |
|---|---:|---:|
| RMSE | **0.321043** | 0.364172 |
| MAE | **0.207367** | 0.219089 |
| R^2 | **0.222835** | approximately 0 |

Relative test RMSE reduction versus training-mean baseline:
**11.8431%**. This is a bounded predictive finding for the original
sequence-dependent bacterial dmsC translation-efficiency phenotype, not a
demonstration of biochemical causation or tissue-regeneration memory.

### Uncertainty

From **600 seeded resamples of the 38,502 held-out genotype units**
(xorshift32 seed `0x7f17329f`), 95% percentile intervals were:

- Selected-model test RMSE: **[0.315342, 0.326453]**.
- Baseline test RMSE: **[0.357541, 0.370494]**.
- Relative RMSE improvement: **[11.5062%, 12.1945%]**.

These are *descriptive genotype-resampling intervals conditional on the
selected model and fixed training/validation split*. They do not include
between-assay batch effects, parameter-selection uncertainty, replicate
variance propagation, or independently replicated wet-lab studies.

## Measured genotype adjacency and tolerance-indexed neutral graph

For all observed dmsC genotype means, an undirected 9-mer single-substitution
Hamming-1 graph was constructed. Of the full cube's 3,538,944 possible
single-nucleotide undirected edges, **3,429,837** connect two genotypes with
an actual dmsC measurement. For a *chosen*, **illustrative** tolerance
`epsilon` in the original mean dmsC response scale, retain an edge when the
absolute difference in the two measured genotype means is at most epsilon.

| Tolerance epsilon | Retained measured edges | Connected components | Singletons | Largest component |
|---|---:|---:|---:|---:|
| 0.05 | 1,004,490 | 15,672 | 12,451 | 233,840 (90.79%) |
| 0.10 | 1,770,810 | 4,558 | 3,817 | 251,609 (97.69%) |
| 0.20 | 2,582,535 | 668 | 616 | 256,823 (99.71%) |

These thresholds were *not* chosen by the experiment's reported
measurement-error distribution. Large components arise from **chains of
small local differences**; neither component membership nor transitive
connectivity means endpoint phenotypes are equal. In particular, these
tolerance networks are **not** established neutral biological attractors,
global Lipschitz classes, or regenerative basins. A further error-aware
neutrality test and source-specific physical dynamics are required.

## Exact reproduction / honest boundaries

```bash
python3 scripts/check_original_dmsc_holdout.py \\
  --original-csv /path/to/cmarti/shine_dalgarno/data/dmsc.csv \\
  --receipt /tmp/dmsc-primary-heldout.json

# Use source-pinned measured replicate adapter for broader ridge analysis:
python3 scripts/prepare_shine_dalgarno_measured.py \\
  --raw /path/to/cmarti/shine_dalgarno/data/dmsc.csv \\
  --out /tmp/dmsc-raw-measured.csv \\
  --manifest /tmp/dmsc-source-manifest.json \\
  --trait-unit 'Log[GFP]'
```

The JSON files above are **ephemeral execution receipts**, not a new
persistent canonical ledger. PostgreSQL PNF remains the only canonical world
model. No source statement, causal equivalence or ontology identity is
promoted by this analysis.

### Remaining experimental max-cut

- Replicate-assay-scale uncertainty, batch effects and a source-grounded
  neutral-network error threshold.
- External held-out studies, not merely a random genotype holdout from one
  experimental campaign.
- Independent perturbation histories and longitudinal bioelectric and
  regenerative morphology for the Levin/planarian claim.
- A mechanism-specific model and competing explanations, with evidence-backed
  physical calibration and prospective controls.

This original-data result closes a **bounded molecular P5 measured-holdout
slice**, not the whole P5 developmental-attractor endpoint.
