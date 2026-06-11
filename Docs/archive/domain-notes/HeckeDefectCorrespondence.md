# Hecke Defect Correspondence

## Scope

This note records the first correspondence operator derived from the signed
multi-lane defect layer rather than from a hand-chosen marked-prime class.

So this is the next step beyond the earlier support-mask correspondence:

- still finite
- still representation-layer only
- but now generated from scan-visible defect behavior

## Landed modules

- [`Ontology/Hecke/DefectCorrespondenceRepresentation.agda`](../Ontology/Hecke/DefectCorrespondenceRepresentation.agda)
- [`Ontology/Hecke/FactorVecDefectCorrespondence.agda`](../Ontology/Hecke/FactorVecDefectCorrespondence.agda)

## What is implemented

For a fixed prime `p` and state `v`:

- vary the paired source prime across all 15 Monster primes
- compute the resulting `PairDefectClass`
- collect those 15 defect values into a finite correspondence fiber

So the new correspondence class is:

> the 15-way defect profile induced by holding one prime fixed and varying the
> paired mode across the Monster basis

The module also adds a genuine finite averaging operator on functions
`PairDefectClass -> Nat`, and a first concrete weighted average:

- `Stable -> 0`
- `Repatterning -> 1`
- `Contractive -> 2`
- `Expansive -> 3`

## Why this matters

This is less synthetic than the earlier support-mask correspondence because
the fiber now comes from the signed scan/defect machinery already present in
the repo.

So the repo now has three Hecke-adjacent flavors:

- reverse-Hecke transport/pullback diagnostics
- quotient-class correspondence on `SupportMask`
- defect correspondence generated from multi-lane transport behavior

## Current boundary

This is still not a classical modular Hecke correspondence.

It is a local finite correspondence on representation-layer defect data.

So the safe claim is:

- the repo now has a nontrivial defect-derived correspondence family
- and a genuine finite averaging operator over that family
- but it is still a Dashi-local representation construction

## Next step

The next honest move is one of:

- connect this defect correspondence to exact chamber classes
- compare defect correspondences across states in the same chamber
- or derive a richer observable-valued correspondence from full defect
  profiles rather than only the coarse defect class

The first two follow-ons are now landed in:

- [`Docs/HeckeDefectProfileCorrespondence.md`](./HeckeDefectProfileCorrespondence.md)
- [`Docs/HeckeChamberDefectCorrespondence.md`](./HeckeChamberDefectCorrespondence.md)
