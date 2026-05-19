# Reverse Hecke Representation Layer

## Scope

This note records the first local implementation of the reverse-Hecke idea
discussed in the archived `Dashi and Physics Insights` thread.

The implementation is intentionally narrow:

- it lives on the representation layer;
- it does not attempt to make reverse-Hecke a conserved quantity of the
  contractive closure dynamics.

## Landed module

The new formal surface is:

- [`Ontology/Hecke/ReverseRepresentation.agda`](../Ontology/Hecke/ReverseRepresentation.agda)

It introduces `ReverseHeckeMetricOn` and `ReverseHeckeMetric`.

## What the module means

The new surface packages five things:

- an address map from states into the 15-prime factor lattice;
- a transport family on states;
- a pullback action on factor vectors;
- a discrepancy scalar;
- a compatibility bit together with a soundness law.

The central law is:

> if the reverse compatibility bit is true, then transporting the state and
> then reading its factor address agrees with pulling back the address directly
> on the prime lattice.

So reverse-Hecke is now represented as:

- state transport on one side,
- prime-lattice pullback on the other,
- discrepancy between the two as the metric.

## What is implemented and what is not

Implemented:

- a reusable representation-layer record;
- a derived Hecke-family view;
- a derived 15-bit signature scan.

Not implemented:

- a concrete nontrivial instance;
- a transport-averaging operator;
- a proof that this metric is preserved by the contractive closure dynamics;
- any lift into the canonical conserved witness.

## Why this is the right boundary

This matches the current repo and archive evidence:

- raw `heckeSignature` fails as a conserved witness under the current
  closure-derived law;
- Hecke/FRACTRAN still belong naturally on prime-lattice coordinates;
- reverse-Hecke therefore belongs first on the representation layer.

## Next step

The next honest move is not to push this module into the conserved bundle.
The first follow-up is now landed separately as a quotient-facing interface:

- [`HeckeQuotientRepresentation.md`](./HeckeQuotientRepresentation.md)
- [`Ontology/Hecke/QuotientRepresentation.agda`](../Ontology/Hecke/QuotientRepresentation.agda)

After that, the next implementation step is to instantiate the pair on a real
prime-address family, likely one built from:

- `FactorVec`,
- the SSP scan pipeline,
- a nontrivial transport family on addressed states.

The first concrete `FactorVec` inhabitant is now landed in:

- [`FactorVecHeckeInstance.md`](./FactorVecHeckeInstance.md)
- [`Ontology/Hecke/FactorVecInstances.agda`](../Ontology/Hecke/FactorVecInstances.agda)
