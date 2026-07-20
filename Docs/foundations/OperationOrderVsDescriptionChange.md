# Operation order versus description change

This note records a narrow conceptual distinction and its current formal status in DASHI.
It is not a claim that either project has completed a derivation of physics.

## The two questions

A Wolfram-style causal-invariance question is:

> If the locally available operations happen in another order, is the same causal structure obtained?

A DASHI description-change question is:

> If the same state is rewritten more compactly, is the observable preserved and does a lawful continuation remain?

The first varies **which operation happens first**. The second varies **how the state is carried or normalised**.

For a discretised trajectory, these become:

- operation-order question: may independent local update atoms be reordered without changing which events can influence which others?
- description-change question: may the trajectory state be canonicalised, reduced, or compressed without changing the named physical observable or destroying the admitted next evolution?

These questions can overlap, but neither implies the other. A system may have a stable canonical form while remaining order-sensitive. A rewrite system may be causally invariant while retaining many inequivalent state descriptions.

## Why this is more than changing units

Changing metres to feet is an invertible relabelling; no information is discarded and the translation back is fixed.

The harder case changes the carrier itself. Examples include resolving carry structure, projecting to a reduced state, integrating out degrees of freedom, changing lattice resolution, or replacing a history with a canonical representative. Such a change must identify what is preserved and prove that the resulting state still belongs to the lawful domain.

The general DASHI test is therefore not merely:

> Can the old description be reconstructed?

It is:

> Does the description-changing operator preserve the named observable, preserve the admitted continuation, reach a canonical state, and become idempotent there?

This does not replace Nyquist theory, statistics, gauge theory, numerical analysis, or renormalisation. Those theories can supply particular preservation theorems. The DASHI layer packages the common proof obligation and keeps unsupported generalisation fail-closed.

## Current checked witness

`DASHI.Physics.Closure.DescriptionChangeLawPreservation` defines the generic proof surface and instantiates it with the existing arithmetic normaliser:

- state: `NormalizeAddState`;
- description-changing operator: `normalizeAdd`;
- observable: `lhs + rhs`;
- lawful continuation: the next normalised state is canonical;
- canonicality: `normalizeAddCanonical`;
- fixed-point law: applying `normalizeAdd` twice equals applying it once;
- MDL connection: `W9MDLTerminationSeamRoute.canonicalMDLTerminationSeamWitness`.

This is a small but real theorem-level example. It proves that one existing canonicalisation changes residue/carry bookkeeping while preserving the selected observable and its admitted canonical continuation.

It does **not** prove:

- arbitrary coarse-graining preserves physical law;
- arbitrary compressed states retain all lawful futures;
- causal invariance under reordered rewrite events;
- a universal renormalisation theorem;
- emergence or derivation of spacetime.

## Relationship to the existing repository

The module reuses rather than duplicates:

- `DASHI.Arithmetic.NormalizeAdd` for canonicalisation;
- `DASHI.Arithmetic.NormalizeAddState` for the state and canonical predicate;
- `DASHI.Arithmetic.NormalizeAddSumPreservation` for the preserved observable;
- `DASHI.Physics.Closure.W9MDLTerminationSeamRoute` for the accepted MDL termination seam and its non-promotion boundaries.

The next substantive extension would require a genuinely physical carrier and an explicit law-preservation theorem, for example a coarse/fine spacetime map that preserves a causal observable and admissible evolution. That extension should instantiate the same proof surface rather than promoting the arithmetic witness into physics by analogy.
