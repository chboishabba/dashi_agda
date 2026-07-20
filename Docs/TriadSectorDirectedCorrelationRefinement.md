# Directed triad-sector correlation refinement

## Status

The current generator taxonomy is closed at the coarse classification layer.  On the
current saturated finite domain, the landed scalar `forcedStableCount` and the
current coarse `DefectOrbitSummary` surfaces are exhausted as splitters.  The next
question is therefore whether ordered sector structure separates any currently
saturated representatives.

## Existing refinement ladder

The current Layer 2 order is:

1. sector-local three-bucket histograms;
2. ordered triad histogram package;
3. symmetric sector dot products;
4. directed cross-bucket interactions.

The first three stages already existed.  The fourth is implemented in
`Ontology/Hecke/TriadSectorDirectedCorrelationRefinement.agda`.

## Why directed interactions are the next minimal object

For a sector histogram

```text
h = (stable, illegal, other)
```

the symmetric dot product retains only

```text
stable_i * stable_j + illegal_i * illegal_j + other_i * other_j.
```

It therefore forgets whether mass flowed from stable to illegal or from illegal to
stable.  The new directed interaction keeps the complete ordered 3 by 3 product
matrix:

```text
stableStable   stableIllegal   stableOther
illegalStable  illegalIllegal  illegalOther
otherStable    otherIllegal    otherOther
```

for the cyclic sector pairs `0 -> 1`, `1 -> 2`, and `2 -> 0`.

This is still finite and purely representation-side.  It does not claim a physical
correlation law, a Monster representation, or that the current saturated branch is
already separated.  It provides the smallest surface that can distinguish routing,
entry/exit asymmetry, and composition-versus-cascade directionality after symmetric
counts have collapsed.

## Predicted discharge order

`Ontology/Hecke/CurrentSaturatedPredictedSectorOrder.agda` records the current
computation order as data rather than prose:

- `balancedCycle` versus `supportCascade`: sector 1, then 0, then 2;
- `balancedComposed` versus `supportCascade`: sector 1, then 2, then 0;
- `denseComposed` versus `fullSupportCascade`: sector 0, then 1, then 2.

For each pair, the directed-correlation comparison is the fallback after all three
sector-local comparisons fail.

## Honesty boundary

The modules expose both possible endpoints:

- a separation witness on the current saturated finite domain; or
- an exhaustion theorem showing that directed correlations also collapse.

Neither endpoint is postulated as a promoted physics result.  The theorem surfaces
are intended for the existing long-compute lane.
