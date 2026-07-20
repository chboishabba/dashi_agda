# Observer-Conditioned Multiscale Transport

## Status

Candidate-only bridge. The checked integration surface is:

- `DASHI.Physics.ObserverConditionedMultiscaleTransport`
- `DASHI.Physics.ObserverConditionedMultiscaleTransportRegression`

It cross-pollinates the existing observer-conditioned transport bridge with:

- `DASHI.Core.MultiscaleMDL`
- `DASHI.Physics.MultiscaleWaveCorrespondence`
- the repository's kernel/project/lift and residual vocabulary
- the existing `CandidateOnlyCore` non-promotion boundary

## Synthesis

The useful synthesis is not simply "track one caustic point". It is:

```text
full transport state
  -> multiscale projection + residual
  -> selected-observer equivalence
  -> temporally persistent relevant carrier
  -> observer decode
```

A fine state and its coarse projection may be equivalent for one selected microphone or pixel while remaining different as full fields. The residual therefore cannot be discarded globally merely because it is invisible at the current observation. It may be needed for another observer, future dynamics, phase recovery, branch topology changes, or later refinement.

## Kernel and lift seam

`KernelTower.project-kernel` already expresses exact scale naturality:

```text
project (K_(j+1) x) = K_j (project x)
```

The new bridge deliberately requires a separate premise when a kernel is claimed to preserve the selected observer. Scale naturality alone does not imply observer invariance, physical correctness, or audible/visible fidelity.

This separates three ideas that were previously easy to conflate:

1. **scale compatibility** — the kernel commutes with projection;
2. **observer compatibility** — the selected observation is preserved;
3. **physical fidelity** — the state and update approximate a chosen wave or transport law.

Only the first two are represented as typed interfaces here, and the second is an explicit supplied premise.

## MDL seam

The exact repository theorem remains:

```text
step description length = coarse cost + residual cost
```

Observer conditioning can rank candidate carriers under this accounting, but it does not establish that:

- MDL is physical action;
- the selected carrier is a minimal sufficient statistic;
- a residual invisible now is safe to delete;
- the representation is rate-distortion optimal;
- the method is computationally faster than RTX or a 3D wave solver.

Those require separate models and receipts.

## Acoustic and light-transport readings

The same typed bridge admits two candidate interpretations:

- a microphone-conditioned acoustic carrier tracking relevant path, mode, or wave-tube contributions;
- a pixel-conditioned light carrier tracking relevant radiance contributors.

A caustic or stationary path can be one sparse residual witness, but the carrier may also require multiple branches, modes, diffuse terms, or volumetric contributions. The formalization therefore rejects a universal single-caustic assumption.

## Where a speed advantage could arise

The plausible advantage is cross-frame reuse of a compact carrier when:

- observer count is small;
- source and geometry evolve smoothly;
- contributor topology changes infrequently;
- decode quality is matched to the reference method;
- discovery and repair costs are amortized.

The required benchmark must report at least:

1. initial contributor discovery cost;
2. per-frame evolution cost;
3. decode cost per microphone or pixel;
4. memory use;
5. temporal and spectral/radiometric error;
6. failure and repair cost at occlusion or branch topology changes;
7. scaling with observer count;
8. matched-quality RTX or wave-solver reference results.

Until those receipts exist, temporal persistence is a mechanism that may enable speedup, not a speedup theorem.
