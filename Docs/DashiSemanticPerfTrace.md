# Dashi semantic perf trace lane

This lane turns the existing DA51/perf witness surface into an explicit semantic
annotation contract.

## Boundary

- `PerfHistory.agda` remains the generated witness/history artifact.
- `perf_da51.py` remains the perf/DA51 producer.
- `DASHI/Perf/SemanticTrace.agda` owns the minimal semantic vocabulary and proves
  that annotation erases exactly to the original surface row.
- `semantic_perf_da51.py` is the initial executable classifier, semantic motif
  miner, and small Fractran compiler.

The initial classifier is intentionally conservative and is not presented as a
complete theorem-derived ontology.  It establishes a checked bridge that can be
refined as more witness families acquire explicit classifications.

## O/R/C/S/L/P/G/F

### O

- surface perf/DA51 records
- Dashi semantic labels
- semantic motif tokens
- ordered Fractran transitions

### R

- preserve all surface data exactly
- attach `dashi_class` and `dashi_family` without mutating counters or hashes
- mine motifs over semantic labels rather than process-local noise
- gate motif promotion by support and an MDL proxy
- compile promoted motifs into deterministic ordered Fractran lanes

### C

```text
DA51 summary
  -> annotate
  -> semantic token projection
  -> semantic motif mining
  -> Fractran compilation
```

### S

```text
SemanticRow = SurfaceRow × DashiClass × DashiFamily
```

The Agda theorem `erase-annotate` proves that the semantic extension is
structure-preserving.

### L

```text
surface record
  < semantically annotated record
  < promoted semantic motif
  < compiled Fractran execution lane
```

### P

The current proposal is the smallest Dashi-native seam: semantic labels are
attached upstream in `dashi_agda`; downstream compressors may use them for motif
identity while retaining the complete surface row for exact reconstruction.

### G

A semantic motif is promoted only when:

- support meets the configured threshold;
- its simple MDL proxy is positive;
- the original records remain recoverable after annotation erasure.

### F

The remaining gap is source authority: the initial Python classifier is explicit
and testable, but only some labels are presently anchored in named witness files.
Future work should replace filename heuristics with generated classifications
from theorem/module metadata where practical.

## Usage

```sh
python3 semantic_perf_da51.py \
  da51_shards/summary.json \
  da51_shards/summary.semantic.json \
  --fractran-output da51_shards/semantic-motifs.fractran.json

python3 test_semantic_perf_da51.py
```

## Formal checks

```sh
agda DASHI/Perf/SemanticTrace.agda
agda DASHI/Perf/Everything.agda
```
