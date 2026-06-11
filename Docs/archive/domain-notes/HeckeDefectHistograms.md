# Hecke Defect Histograms

## Scope

This note records the first histogram layer above the defect-derived Hecke
correspondence on the `FactorVec` representation carrier.

Relevant modules:

- [`Ontology/Hecke/FactorVecDefectHistograms.agda`](../Ontology/Hecke/FactorVecDefectHistograms.agda)
- [`Ontology/Hecke/FactorVecChamberDefectHistograms.agda`](../Ontology/Hecke/FactorVecChamberDefectHistograms.agda)

## What is now implemented

For each fixed target prime `p` and state `v`, the existing 15-entry defect
correspondence fiber is now summarized in two ways:

- a full defect-class histogram:
  counts of `Stable`, `Repatterning`, `Contractive`, and `Expansive`;
- an illegal / forced-stable count:
  the number of entries whose paired mode is illegal, equivalently the number
  of entries whose defect is forced to `Stable` by illegality alone.

This is deliberately weaker than a claim that the full defect histogram is a
chamber invariant.

## The first proved chamber law

Exact chamber agreement already means equality of the full legality signature
for every `PairMode`.

That immediately fixes the illegal mask for a chosen prime `p`, so the repo
now proves:

- if two states lie in the same exact `PairMode` chamber,
- then they have the same `illegalCount` for that prime;
- equivalently they have the same `forcedStableCount`.

This is the first histogram-level chamber invariant for the current defect
correspondence.

## Stronger claim already ruled out

The next stronger statement is now known to fail.

See:

- [`Docs/HeckeDefectHistogramObstruction.md`](./HeckeDefectHistogramObstruction.md)
- [`Ontology/Hecke/FactorVecHistogramObstruction.agda`](../Ontology/Hecke/FactorVecHistogramObstruction.agda)

The repo now has a concrete counterexample showing that two states can share
the same pointwise exact legality signature while still having different full
defect histograms.

## What is not yet claimed

The repo still does **not** claim that:

- full defect-profile correspondences are constant on exact chambers;
- compressed chamber carriers already preserve the same information.

So this layer should be read as:

> histogram extraction is now landed, the forced-stable / illegal component is
> proved chamber-invariant, and the full-histogram chamber law is already
> falsified by a concrete counterexample.

## Next seam

The next honest theorem targets are:

- test whether full defect-profile correspondences collapse to chamber
  invariants or only to weaker orbit-style families;
- identify coarser histogram summaries that really are chamber-stable;
- only then attempt compressed chamber quotients driven by proved-stable
  histogram or profile data.
