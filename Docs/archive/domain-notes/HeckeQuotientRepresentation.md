# Hecke Quotient Representation

## Scope

This note records the next interface-level step suggested by the refreshed
`Dashi and Physics Insights` thread:

- define an equivalence relation,
- package a quotient interface,
- let Hecke act on quotient classes or fibres,
- avoid pretending full quotient elimination is already available.

## Landed module

- [`Ontology/Hecke/QuotientRepresentation.agda`](../Ontology/Hecke/QuotientRepresentation.agda)

It introduces three interface records:

- `EquivalenceOn`
- `QuotientInterfaceOn`
- `QuotientHeckeActionOn`

## What the module does

The module gives the minimal lawful surface for quotient-style Hecke work on a
representation family:

- `EquivalenceOn` packages a setoid-like relation on states;
- `QuotientInterfaceOn` adds a class carrier, projection, and chosen
  representatives;
- `QuotientHeckeActionOn` states that a transport family respects the
  equivalence relation and descends to a Hecke action on quotient classes.

This is the safe first step because the repo does not yet require a concrete
computational quotient or cubical quotient elimination.

## What it is not

This module does not yet provide:

- a concrete agreement relation;
- a basin-derived quotient;
- a nontrivial Hecke action instance;
- a bridge into the contractive closure dynamics.

## Relation to reverse-Hecke

This note complements
[`ReverseHeckeRepresentation.md`](./ReverseHeckeRepresentation.md).

The current clean split is:

- reverse-Hecke packages transport versus pullback on the prime lattice;
- quotient-Hecke packages the equivalence/class interface required for Hecke to
  act on classes rather than on a single evolving state.

## Next step

The next honest move is to instantiate this surface with a real agreement
relation, likely one derived from:

- factor-address agreement,
- basin collapse,
- or a coarse observable quotient on the representation layer.

The first concrete inhabitant is now landed in:

- [`FactorVecHeckeInstance.md`](./FactorVecHeckeInstance.md)
- [`Ontology/Hecke/FactorVecInstances.agda`](../Ontology/Hecke/FactorVecInstances.agda)
