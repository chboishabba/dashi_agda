# Operation order versus representation change

This note records a conceptual distinction and its current formal status in DASHI. It is not a claim that either DASHI or the Wolfram Physics Project has completed a derivation of physics.

## The two questions

A Wolfram-style causal-invariance question is:

> If the locally available operations happen in another order, is the same causal structure obtained?

The stronger DASHI representation question is:

> If the same system is carried at another resolution, in another basis, or through a reduced description, does the kernel still describe the same admissible evolution and the same dynamical shapes?

The first varies **which operation happens first**. The second varies **the form through which the state and its dynamics are represented**.

For a discretised trajectory:

- operation-order question: may independent update atoms be reordered without changing which events can influence which others?
- representation question: may the trajectory be projected, canonicalised, compressed, or refined while preserving the evolution law, admitted states, observables, and relevant fixed points or attractors?

These questions overlap but neither implies the other. A system may have a stable canonical representation while remaining order-sensitive. A rewrite system may be causally invariant while two coarse representations obey different effective dynamics.

## The real DASHI test is a commuting kernel square

The earlier narrow formulation asked whether a description change preserved one observable and a lawful continuation. That remains useful for one-state canonicalisation, but the full operator question is stronger:

```text
fine state  -- fine kernel -->  evolved fine state
    |                              |
 projection                    projection
    |                              |
    v                              v
coarse state -- coarse kernel -> evolved coarse state
```

The representation change preserves the law when the two routes agree, exactly or through a named residual/equivalence:

```text
project (fineStep x)  =  coarseStep (project x)
```

This is already the central condition in `DASHI.Physics.Refinement`: its exact refinement step requires `project (step₁ x) ≡ step₀ (project x)`, while `ApproxRefinementStep` carries the same obligation through an explicit approximate relation.

This is why the DASHI question is not merely “can the original signal be reconstructed?” or “does a statistic remain close?” It asks whether the **operator itself survives the change of representation**.

## Why this is more than changing units

Changing metres to feet is an invertible relabelling. The state space and the dynamics have not actually been reduced.

The harder changes include:

- projecting a fine field to a coarse field;
- integrating out degrees of freedom;
- changing lattice or refinement depth;
- replacing a state by a canonical quotient representative;
- retaining only support, sign, phase, residue, or another structured carrier;
- transporting a kernel between those carriers.

A lawful change must say what counts as the same physics and prove that the kernel respects that relation. Numerical closeness, reconstructability, statistical insignificance, or low description length do not establish this by themselves.

## Fixed points and attractors

Kernel compatibility gives a concrete structural payoff. If an admissible fine state is a fixed point,

```text
fineStep x = x
```

and projection commutes with the kernel, then the projected state is a coarse fixed point:

```text
coarseStep (project x) = project x
```

`DASHI.Physics.Closure.RepresentationKernelCompatibility.projectedFixedPoint` proves this elementary transport theorem.

This is the first rigorous part of the “shape” language: the preserved object is not merely a scalar measurement but a dynamical shape. Full attractor or basin preservation is stronger and still requires a metric, neighbourhood/basin definition, convergence law, and projection-stability theorem.

The uploaded attractor/retrocausality discussion is therefore relevant only at this bounded point: a future or terminal object can constrain the selected history through fixed-point, boundary, or admissibility structure without establishing literal retrocausal physical influence. The module explicitly does not promote retrocausality.

## Admissibility, equivalence, and MDL have different jobs

The cross-pollinated operator separates three layers:

1. **Admissibility** says which states and transitions belong to the lawful domain.
2. **Kernel compatibility** says whether evolution survives projection or redescription.
3. **MDL** chooses a cheaper canonical representative inside an equivalence class already shown to preserve the physics.

This order matters. MDL does not make two states physically equivalent merely because one is shorter. The new `MDLRepresentativeSelection` surface therefore requires:

- an explicit same-physics relation;
- preservation of that relation by canonical selection;
- non-increasing description cost;
- idempotence of the canonical representative.

That matches the existing repository split between checked invariance/closure claims and selection or termination seams.

## Current checked surfaces

`DASHI.Physics.Closure.DescriptionChangeLawPreservation` remains the small concrete one-state witness:

- state: `NormalizeAddState`;
- canonicalisation: `normalizeAdd`;
- observable: `lhs + rhs`;
- admitted continuation: the next state is canonical;
- fixed-point law: normalising twice equals normalising once;
- MDL connection: `W9MDLTerminationSeamRoute.canonicalMDLTerminationSeamWitness`.

`DASHI.Physics.Closure.RepresentationKernelCompatibility` adds the broader operator-level surface:

- exact fine/coarse kernel compatibility;
- admissibility transport;
- observable transport;
- projected fixed-point theorem;
- approximate compatibility through an explicit same-physics relation;
- MDL canonical representative selection only after equivalence is supplied.

The module cross-references rather than replaces `DASHI.Physics.Refinement`, whose project/evolve commuting law is the existing formal seed.

## What remains open

The new surface does **not** prove:

- arbitrary coarse-graining preserves physical law;
- every attractor or basin survives projection;
- reordered operations are causally invariant;
- a universal renormalisation theorem;
- emergence of spacetime or quantum mechanics;
- retrocausal influence;
- that minimum description length identifies physical truth.

A substantive physics instance now has a clear target: instantiate the compatibility square on a physical fine/coarse carrier, provide its admissibility and observable maps, state the exact or residual equivalence, and prove that the appropriate dynamics commute with projection.
