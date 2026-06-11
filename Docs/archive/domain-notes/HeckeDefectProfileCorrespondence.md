# Hecke Defect Profile Correspondence

## Scope

This note records the next lift beyond the coarse defect-class correspondence.

Instead of keeping only:

- `Stable`
- `Repatterning`
- `Contractive`
- `Expansive`

the new correspondence fiber keeps the full finite `PairDefectProfile`.

## Landed module

- [`Ontology/Hecke/FactorVecDefectProfileCorrespondence.agda`](../Ontology/Hecke/FactorVecDefectProfileCorrespondence.agda)
- [`Ontology/Hecke/FactorVecChamberDefectProfileCorrespondence.agda`](../Ontology/Hecke/FactorVecChamberDefectProfileCorrespondence.agda)

## What is implemented

For a fixed prime `p` and state `v`:

- vary the paired source prime across all 15 Monster primes
- collect the full `PairDefectProfile` at each entry

So the correspondence now retains:

- pre/post signatures
- drift
- pre/post motifs
- coarse defect class

The module also adds a first weighted average on full profiles:

- `profileWeight = drift + defectClassWeight`

The next local compression layer is now also landed:

- [`Docs/HeckeDefectOrbitSummaries.md`](./HeckeDefectOrbitSummaries.md)
- [`Ontology/Hecke/FactorVecDefectOrbitSummaries.agda`](../Ontology/Hecke/FactorVecDefectOrbitSummaries.agda)

## Why this matters

This is the first correspondence that keeps more than just the coarse defect
label.

So the next questions can now be asked on a richer fiber:

- which parts of the profile are chamber-stable
- which parts vary inside a chamber
- which weights or observables are the right ones to average
- which coarser orbit-style summaries survive when the full histogram does not

The chamber-side restriction is now also lifted to this fuller carrier:

- if an entry `(q , p)` is illegal on one state in an exact chamber,
- then on every other state in that chamber the corresponding full profile
  entry has:
  - zero signature drift,
  - no motif change,
  - and coarse defect class `Stable`.

## Current boundary

This is still a local finite representation-layer correspondence.

It is richer than the coarse defect-class fiber, but it is not yet an orbit
classification or a modular correspondence.
