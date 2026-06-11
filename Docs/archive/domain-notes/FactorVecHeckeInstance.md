# FactorVec Hecke Instance

## Scope

This note records the first concrete instantiation of the new representation
layer Hecke surfaces.

The carrier is the existing 15-prime factor vector itself.

## Landed module

- [`Ontology/Hecke/FactorVecInstances.agda`](../Ontology/Hecke/FactorVecInstances.agda)

## What it instantiates

The module provides:

- a concrete equality-level equivalence on `FactorVec`;
- a concrete coarser support-mask equivalence on `FactorVec`;
- a concrete equality quotient interface with `FactorVec` as both state and
  class carrier;
- a concrete nontrivial quotient interface with `SupportMask` as the class
  carrier;
- a concrete reverse-Hecke metric on `FactorVec`;
- a concrete quotient-Hecke action on `FactorVec`.

## Current transport law

The first concrete transport is intentionally simple but nontrivial:

- for each Monster prime `p`,
- `bumpPrime p` increments the corresponding exponent lane in the factor
  vector.

The module now also contains a richer alternate family:

- `flowPrime p`
- first bumps the selected prime lane,
- then bumps the next prime lane in the fixed Monster ordering.

That means the current instance now has:

- a one-lane prime-address action, and
- a two-lane local prime-flow action,

but still not yet a modular correspondence or transport average.

The newer quotient action uses the coarser `SupportMask` carrier:

- two factor vectors are equivalent when they activate the same prime support
  pattern;
- the class action marks the selected prime as present.

The alternate quotient action uses `flowMask`:

- it marks the selected prime as present,
- and also marks the next prime in the fixed ordering.

## Why this is still useful

This instance is enough to prove that the new representation-layer interfaces
are not just abstract sketches:

- they are inhabited;
- they compile;
- they act on a real prime-address carrier already present in the repo.

## What it is not

This is not yet:

- a realistic Hecke correspondence;
- a quotient induced by basin/agreement collapse;
- a bridge into the contractive closure bundle.

It is the first concrete representation-layer inhabitant, now with both:

- a trivial equality quotient, and
- a genuinely coarser support-mask quotient.

## Next step

The next honest upgrade is one of:

- replace equality with a coarser agreement relation on factor vectors;
- replace `bumpPrime` with a richer transport family;
- connect this instance to a real prime-embedding / scan pipeline.

The first of those is now partially landed via the `SupportMask` quotient, so
the transport family was the next best upgrade and is now also partially
strengthened via `flowPrime`.

The next honest upgrade is no longer “add another trivial transport variant.”
It is to connect these concrete actions to a more meaningful prime-address
family or scan pipeline.
