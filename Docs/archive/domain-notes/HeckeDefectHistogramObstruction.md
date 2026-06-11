# Hecke Defect Histogram Obstruction

## Scope

This note records the first concrete obstruction on the histogram layer above
the defect-derived Hecke correspondence.

Relevant module:

- [`Ontology/Hecke/FactorVecHistogramObstruction.agda`](../Ontology/Hecke/FactorVecHistogramObstruction.agda)

## Result

The stronger chamber claim is false:

> full defect histograms are **not** determined by the exact legality-signature
> data alone.

The repo now contains a concrete counterexample built from two small
`FactorVec` states:

- `counterexample-x` has exponent `2` on the `p7` lane and zero elsewhere;
- `counterexample-y` has exponent `3` on the `p7` lane and zero elsewhere.

These two states have the same pointwise `PairMode` legality signature, but
their full defect histograms for target prime `p7` differ:

- for `counterexample-x`, one entry is `Repatterning`;
- for `counterexample-y`, the corresponding entry is `Expansive`.

So the chamber-invariant part of the histogram is currently only the
forced-stable / illegal component, not the whole histogram.

## Consequence

The next honest theorem target is no longer:

- prove full defect-histogram constancy on exact chambers.

That statement is now known to fail.

The next honest targets are instead:

- identify coarser histogram summaries that are chamber-stable;
- test whether fuller defect-profile correspondences stabilize only at an
  orbit-style level rather than at chamber level;
- derive compressed chamber summaries from proved-stable statistics rather than
  from the raw full histogram.
