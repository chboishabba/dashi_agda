# Hecke Correspondence Representation

## Scope

This note records the first genuine correspondence-class Hecke operator on the
representation layer.

The target was the Ope-style shape:

- a nontrivial correspondence class `[x]`
- and a true sum-over-correspondence operator

The current repo now has that in a local finite form on the `SupportMask`
quotient carrier.

## Landed modules

- [`Ontology/Hecke/CorrespondenceRepresentation.agda`](../Ontology/Hecke/CorrespondenceRepresentation.agda)
- [`Ontology/Hecke/FactorVecCorrespondence.agda`](../Ontology/Hecke/FactorVecCorrespondence.agda)

## What is implemented

The abstract module adds:

- `PrimeCorrespondenceHeckeOn`
- `correspondence : SSP -> Class -> Vec15 Class`
- `operator : (Class -> Nat) -> SSP -> Class -> Nat`

where the operator is a genuine finite sum over the correspondence fiber.

The first concrete instance uses the existing `SupportMask` quotient class:

- fix a prime `p`
- mark `p` as present
- then vary a second marked prime across all 15 Monster primes

So the correspondence class is finite and nontrivial, and the resulting Hecke
operator really has the form:

> `(T_p f)(x) = Σ_{y in [x]_p} f(y)`

for the current finite correspondence family `[x]_p`.

## Why this matters

This is stronger than the earlier transport-only or quotient-only Hecke
surfaces.

The repo now has both:

- reverse-Hecke diagnostics for transport vs pullback
- and a true correspondence-sum operator on quotient classes

That is the first local implementation of the two Hecke flavors we discussed.

## Current boundary

This is still a finite representation-layer correspondence, not a classical
modular Hecke correspondence.

So the safe claim is:

- the repo now has a nontrivial correspondence class on `SupportMask`
- and a genuine averaging Hecke operator over that class
- but not yet a modular-curve or moonshine-level Hecke theorem

## Next step

The next honest move is one of:

- connect this correspondence operator to the signed scan/motif layer
- derive a correspondence from transport-generated chamber or defect data
- or replace the current marked-prime correspondence with a richer
  scan-derived family

The first scan/defect-derived follow-on is now landed in
[`Docs/HeckeDefectCorrespondence.md`](./HeckeDefectCorrespondence.md).
