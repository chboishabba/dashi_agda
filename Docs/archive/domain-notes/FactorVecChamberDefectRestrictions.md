# FactorVec Chamber Defect Restrictions

## Scope

This note records the first theorem-level bridge from the exact chamber layer
to the multi-lane defect layer.

The statement is intentionally narrow:

- exact chamber agreement does not determine every defect outcome;
- but it does force `Stable` behavior for any mode that is illegal throughout
  that chamber.

## Landed module

- [`Ontology/Hecke/FactorVecChamberDefectRestrictions.agda`](../Ontology/Hecke/FactorVecChamberDefectRestrictions.agda)

## What is implemented

The module proves:

- if two states lie in the same exact `PairMode` chamber, then legality of a
  chosen mode agrees between them;
- therefore, if that mode is illegal on one state, it is illegal on the other;
- and because illegal modes use `transportOrStay`, the resulting defect class
  is forced to `Stable`.

So the first chamber-to-defect bridge is:

> chamber agreement propagates illegal-mode stability.

## Why this matters

This is the first nontrivial restriction on defect behavior obtained from the
exact chamber carrier.

It still does not say:

- that exact chambers determine all defect classes;
- that a smaller threshold carrier is sound;
- or that orbit structure has already been solved.

But it does show the chamber layer is beginning to control observable
post-transport behavior rather than only legality bits in isolation.

## Next step

The next honest move is:

- find stronger chamber-side restrictions on `Repatterning`, `Contractive`,
  and `Expansive` behavior;
- or cluster defect profiles into orbit-style families and then ask what
  chamber information is sufficient to recover those families.
