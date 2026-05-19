# Hecke Chamber Defect Correspondence

## Scope

This note records the first chamber-side theorem stated directly on the
defect-derived correspondence entries.

## Landed module

- [`Ontology/Hecke/FactorVecChamberDefectCorrespondence.agda`](../Ontology/Hecke/FactorVecChamberDefectCorrespondence.agda)

## What is implemented

For any chosen entry `(q, p)` in the defect-derived correspondence:

- if two states lie in the same exact chamber
- and the paired mode `(q, p)` is illegal on one of them
- then the correspondence entry at `(q, p)` is forced to `Stable` on the
  other

So the earlier chamber-to-defect restriction is now expressed directly on the
new defect-derived correspondence family.

## Why this matters

This is the first direct bridge between:

- exact chamber agreement
- and correspondence-level Hecke data

It still only controls the illegal/stable case, but it now does so at the
fiber-entry level of the new correspondence family rather than only on the raw
mode defect function.
