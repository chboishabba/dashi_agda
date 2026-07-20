# Representation/kernel coherence

This tranche turns the foundations discussion into one canonical theorem stack.

## Central question

The DASHI representation question is not merely whether a compressed state keeps one selected number. It is whether changing the carrier preserves the action of the kernel:

```text
project (fineStep x) = coarseStep (project x)
```

on admissible states.

The operation-order question is separate: if locally available operations are scheduled differently, does the same causal or physical structure result? The two axes can eventually be combined, but neither is silently assumed by the other.

## Landed theorem stack

`DASHI.Physics.Closure.RepresentationKernelCompatibility` provides:

- exact fine/coarse carrier compatibility;
- admissibility transport;
- observable transport;
- a derived n-step trajectory theorem;
- a derived fixed-point projection theorem;
- a derived finite-reachability basin theorem;
- an explicit same-physics data structure separating observables, invariants, causal support, and admissibility;
- approximate compatibility with a named n-step defect and budget;
- MDL representative selection only inside an already supplied physical equivalence relation.

`DASHI.Physics.Closure.RepresentationKernelRefinementBridge` connects this canonical interface to the pre-existing `DASHI.Physics.Refinement` exact commuting-square spine.

`DASHI.Physics.Closure.RepresentationAttractorTransport` records the extra metric and convergence obligations required to upgrade finite reachability into a genuine attractor/basin theorem.

`DASHI.Physics.Closure.ScheduleRepresentationCoherence` records the eventual two-axis interface: vary both the representation and an admissible update schedule while preserving the same coarse physics.

## First physical witness

`DASHI.Physics.Closure.TwoChannelTransportRepresentationWitness` is a deliberately minimal physical/dynamical instance.

- Fine state: two directed transport channels `(left , right)`.
- Fine kernel: exchange the two channels.
- Coarse state: total transported content.
- Projection: `left + right`.
- Coarse kernel: identity on total content.

The central theorem is exact because exchanging channels preserves total transported content. The generic n-step theorem therefore gives zero accumulated representation defect for every number of iterations.

The witness is also packaged through the existing `PhysicalTheory` record, and as an approximate law with zero defect and zero budget. Its MDL representative is intentionally the identity: this demonstrates the correct ordering of proof obligations without fabricating a compression gain.

## Logical order

```text
admissibility
    -> kernel/representation compatibility
    -> trajectory or bounded-defect coherence
    -> physical equivalence class
    -> MDL representative selection
```

Low description length does not establish physical equivalence. MDL is a selector after the physical relation has been proved or explicitly assumed.

## What is proved

For every exact compatibility law and admissible fine state:

```text
project (iterate fineStep n x)
  = iterate coarseStep n (project x)
```

Fine fixed points project to coarse fixed points. Fine states that reach a target in finitely many steps project to coarse states that reach the projected target in the same number of steps.

For the two-channel transport witness, these results are concrete theorem-level facts.

## What remains open

The tranche does not prove:

- arbitrary coarse-graining preserves physics;
- a continuum wave or spacetime representation theorem;
- a nonzero quantitative defect estimate derived from local consistency and stability assumptions;
- preservation of every attractor, basin, topology, or orbit class;
- Wolfram-style causal invariance for arbitrary update schedules;
- that MDL or compression determines physical truth.

The next substantive physical result should replace the exchange witness with an existing DASHI wave, shift, lattice, or finite-propagation carrier and prove either exact commutation or a derived bound

```text
defect n x <= budget n
```

where the budget follows from one-step consistency plus a stability or contraction theorem rather than being postulated as a field.
