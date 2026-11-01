# Art's hidden topology in DASHI

This lane formalises the paper by Dmitruk et al., *Art's hidden topology: A window into human perception* (PLOS Computational Biology, 14 May 2026, DOI `10.1371/journal.pcbi.1014156`). It is a source-bound computational-topology/perception bridge, not a theorem defining art, beauty, artistic intent, or aesthetic value.

## Typed flow

```text
2D image
  -> paired cubical filtrations (black-to-white / white-to-black)
  -> persistent H0/H1 cycles
  -> integrated Betti areas
  -> Alexander-duality residuals
  -> spatial feature maps
  -> gaze-map contact
  -> source-bound empirical claims
```

`DASHI.Topology.VisualPersistentHomologyCore` records persistence intervals and four integrated Betti-area lanes:

```text
BW-H0, BW-H1, WB-H0, WB-H1.
```

The two duality comparisons are:

```text
BW-H0 against WB-H1
WB-H0 against BW-H1.
```

For paired areas `A` and `B`, the paper's normalized violation measure is represented division-free as:

```text
numerator   = 2 * |A - B|
denominator = A + B
ADV         = numerator / denominator
```

Keeping numerator and denominator separate avoids floating-point authority and preserves exact finite arithmetic. A rational target `p/q` is compared by the cross-multiplied residual:

```text
|q * numerator - p * denominator|.
```

The reported cluster near `0.4` is therefore encoded as the candidate target `2/5`. A toy regression proves that the socket recognizes an exact `2/5` ratio; it does not assert that any artwork has that value.

## DASHI interpretation

The structural carrier is not the raw pixel matrix alone. It is the paired multiscale filtration and its persistent-cycle signature. Alexander-duality failure is not generic contradiction pressure: in this construction it is specifically a boundary/frame interaction residual between opposing filtration/dimension lanes.

The gaze bridge uses observable contact geometry:

```text
feature-map cell x gaze-map cell -> shared spatial region.
```

This records correspondence only. It does not prove causation, aesthetic value, stable neural integration, or recovery of artist intent. Laboratory and gallery conditions are also kept non-interchangeable because the study reports context effects and avoids direct cross-setting comparisons for several analyses.

## Promotion boundary

The following remain false:

```text
golden rule = universal aesthetic law
persistent homology separates all art from all AI imagery
topology determines aesthetic experience
gaze contact recovers artist intent
source report = DASHI empirical/scientific/cultural authority
```

The implementation preserves the paper's reported claims while preventing media-language escalation from “cluster near 0.4 in these sampled works” to “mathematical law of art”.

## Next mathematical work

1. Implement finite greyscale images and the V-construction cubical complexes.
2. Compute BW/WB filtrations and persistent H0/H1 intervals rather than accepting signatures as inputs.
3. Prove the finite dual pairing away from frame-touching cycles.
4. Derive integrated Betti areas from the computed barcodes.
5. Ingest the authors' public code/data as an external validation artifact.
6. Reproduce the reported group statistics and target distribution under explicit dataset/version hashes.
