# FactorVec Multi-Lane Defects

## Scope

This note records the first defect layer above the exact chamber surface for
the multi-lane signed `FactorVec` transport.

The point is not to claim a chamber quotient already determines transport
outcomes. It does not. The point is to expose what the transport does to the
existing signed scan and motif observables.

## Landed module

- [`Ontology/Hecke/FactorVecMultiLaneDefects.agda`](../Ontology/Hecke/FactorVecMultiLaneDefects.agda)

## What is implemented

For each `PairMode` and `FactorVec`, the module computes:

- pre-transport signed scan signature
- post-transport signed scan signature
- signature drift
- pre/post signed motif
- a first defect classifier:
  - `Stable`
  - `Repatterning`
  - `Contractive`
  - `Expansive`

The post state is taken through the existing multi-lane `transportOrStay`
surface, so illegal modes are handled honestly.

## Why this matters

The exact chamber carrier tells us which modes are legal.

This new defect layer tells us what a legal or failed mode does to the signed
scan observables already present on the representation layer.

That is the right next step after:

- proving that coarse quotients were too lossy for signed transport;
- landing the exact legality-signature chamber surface.

## Current boundary

This is still a first defect surface:

- the defect classes are scan-derived, not yet orbit-theoretic;
- no theorem says exact chambers determine defect class;
- no compressed chamber carrier is claimed yet.

So the safe claim is:

> the repo now compares signed scan and motif observables before and after
> multi-lane transport, and classifies the resulting representation-layer
> defect into a first small family.

## Next step

The next honest move is one of:

- relate exact chamber agreement to restrictions on possible defect classes;
- cluster defect profiles further into orbit-style families;
- or prove that some smaller chamber carrier is complete for legality while
  still leaving defect behavior explicit.

The first restriction theorem is now landed in
[`Docs/FactorVecChamberDefectRestrictions.md`](./FactorVecChamberDefectRestrictions.md).
