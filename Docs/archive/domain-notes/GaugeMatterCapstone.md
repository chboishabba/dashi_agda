# Gauge/Matter Recovery Capstone

This note synthesizes the upstream `P0` lanes for realization independence,
natural dynamics, conserved quantities, and the continuum limit into one
statement of what a full gauge/matter recovery theorem would actually require.

## Theorem target

A full recovery theorem should connect:

1. an abstract carrier with an admissible dynamics law;
2. a conserved-observable layer that survives gauge actions and coarse flows;
3. a continuum-lift layer that maps finite witnesses into field-like objects;
4. a realization-independent comparison principle showing that admissible
   carriers recover the same gauge/matter observables.

## Inherited machinery

- [`RealizationIndependence.md`](./RealizationIndependence.md) already isolates
  the abstract hypotheses hidden inside the canonical shift proofs:
  coarse-pair commutation, cone preservation, and admissibility transport.
- [`DynamicsInvariantGapChecklist.md`](./DynamicsInvariantGapChecklist.md)
  sharpens the current bottleneck:
  the repo already has execution, basin, cone, and signature surfaces, but
  several of the strongest witnesses remain canonical-only or partially
  trivialized rather than realization-independent.
- [`NaturalDynamicsLaw.md`](./NaturalDynamicsLaw.md) gives the minimum
  dynamics-law shape: state, evolve/coarse maps, admissibility, and MDL-style
  descent.
- [`ConservedQuantities.md`](./ConservedQuantities.md) identifies the current
  best invariant candidates:
  MDL level, cone compatibility, and finite Hecke/eigen observables.
- [`ContinuumLimit.md`](./ContinuumLimit.md) states what a limit theorem would
  need: scaling parameters, limit carriers, and invariant-preservation claims.

## Main blockers

- No abstract gauge bundle/carrier record currently sits above the
  package-parametric gauge theorems.
- Conserved observables are not yet lifted into a generic gauge-invariant
  surface shared by multiple realizations.
- The current coarse/evolution theorems do not yet prove gauge-sector
  persistence at the abstract carrier level.
- The continuum side is still described only as a requirement set, not as a
  theorem-facing record instantiated by closure modules.

## Promotion order

1. Introduce an abstract gauge/matter bundle record above the current
   package-parametric gauge layer.
2. Attach a realization-independent natural-dynamics witness and
   conserved-observable witness to that bundle.
3. Add a continuum witness record stating how bundle observables lift to a
   limit carrier.
4. Only then state the full gauge/matter recovery theorem over that abstract
   bundle surface.

## Current promotion step

Step 1 is now landed:

- the abstract bundle layer exists;
- the canonical package inhabits it;
- the live shift RG surface is imported through a carrier-level transport;
- the canonical bundle dynamics are non-identity;
- and the canonical bundle `mdlLevel` now comes from the transported live
  `RGObservable`.

The next proof-bearing seams are now:

1. strengthen the conserved quantity further from the now-landed
   `Gauge × mdlLevel × motifClass` witness toward a defensible larger
   `RGObservable`-level invariant, if additional transported channels can be
   shown stable under bundle dynamics;
2. strengthen the now-landed theorem-bearing continuum witness beyond its
   current first quotient-like limit carrier.

The former “connect offset universality into the bundle story” seam is now
closed at the first conversion level: the abstract bundle theorem exports an
`ObservableRGOffsetUniversality` witness, and the canonical bundle instance
inhabits it.

The former “replace the synthetic dynamics” seam is now closed at the first
honest level: the canonical bundle uses the closure-derived law
`x ↦ [ CR , x ]` instead of a hand-written carrier cycle.

The projection/Δ side has also tightened one step further:

- the abstract recovery theorem now carries a transported
  projection/Δ witness as part of its own proof payload;
- it now also carries the alternate transported phase family on the same
  abstract surface, so the recovery theorem no longer hardcodes one target-side
  projection schedule pair;
- this means target-side schedule compatibility is no longer only exported in
  parallel from the bundle layer, but is now required proof mass on the same
  abstract theorem surface.

The remaining seam there is narrower:

1. keep promoting the inhabitant away from the current canonical live-shift
   family rather than only adding new conversions around it;
2. continue the conserved-quantity and continuum work without reopening the
   basic projection/Δ abstraction question.
