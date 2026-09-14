# Navier–Stokes proof-control record — 15 September 2026

Status: active proof-search control document; non-promoting.

This document replaces neither the historical roadmaps nor their source
owners.  It records the current division of labour and active search priority
so that work is not sent back through the entire historical round graph merely
because that graph remains valuable donor material.

## Objective and operating rule

The objective is to solve the unforced DASHI Navier–Stokes programme with
actual Lean proof receipts.  The complete Agda, Lean, archived, and published
corpus is active proof material and searchable donor space.  Historical routes
are maps, not mandatory premises: a worker may bypass, strengthen, or replace
one only by recording the exact endpoint, hypotheses, consumer, provenance,
and relation to the displaced route.

No statement may be promoted from source provenance, a Boolean ledger, a
conditional compiler surface, or a similarly named theorem.

## Three distinct jobs

### C/D — published forced-breakdown proof

The official `openai/NavierStokesAndEuler` source has two public snapshots:

| snapshot | role |
| --- | --- |
| `8937a8f4…` | initial public release snapshot |
| `f9e8bc5b38b6e212696e8a30e3e91517af887bbd` | current observation, 2026-09-10; adds `NavierStokes.PaperResults` to the top-level surface |

The public roots are:

```text
NavierStokes.Comparator.navier_stokes_breakdown_R3
NavierStokes.Comparator.navier_stokes_breakdown_periodic
```

They establish forced breakdown alternatives C and D.  Work here is source
lineage, independent checking, dependency closure, and same-object carrier
integration.  It is not discovery of an A/B proof.  Preserve the old source
observation append-only; never overwrite it with the newer observation.

The existing C/D-to-DASHI statement alignment remains useful.  The first
representation seam is the concrete released candidate/field/forcing to the
DASHI Fourier/R406 carrier.  A released theorem does not itself pay that weld.

### A — active independent unforced proof search

The current primary target is:

```text
CommutatorOnlySpacetimeBudget568
```

Its intended content is a cutoff-uniform bound

```text
4 * integral[0,T] globalForcingFull(N,t) dt <= B(T).
```

The recommended first route is R571 through the literal signed `+y/-y`
multiplier-difference carrier, then existing centered/Taylor, six-three,
inner-fibre, resolvent, spectator, and full-square machinery toward R568.
Use signed structure before positive Schur majorisation.  R577's four-positive-
receipt construction is a fallback, not a mandatory first route.

The true terminal work is two independent payments:

```text
A1  CommutatorOnlySpacetimeBudget568
A2  literal R406 phase-sensitive critical-production estimate
```

Neither payment may be used to silently discharge the other.  Only after both
exist may the already-constructed R414/R104/barrier compiler cascade be run.

### B — deferred unforced periodic/global consumer

B remains an independent target unless a genuine transport theorem is built.
It is deferred for Pareto reasons, not because A automatically proves B.
Reuse A machinery only through exact typed transport.

## What is donor material, not mandatory rework

Do not spend the first proof-search pass rediscovering Fourier representation,
signed commutator algebra, Waleffe geometry, primitive R574 control,
fibre/global aggregation, resolvent symmetry, spectator rows, transpose/full-
square collapse, the `C_direct` identification, or the R145-to-R584
archaeology.  Search and reuse them where their actual consumer factors
through the existing carrier.

## Required delivery discipline

For every new Lean result or proposed replacement, report:

1. exact theorem endpoint and consumer;
2. source/Agda/Lean lineage and any same-object map;
3. hypotheses and axiom receipt;
4. whether it pays A1, A2, C/D integration, or only infrastructure;
5. the remaining unpaid seam.

Completion means actual Lean receipts for the named payment(s) and their
consumer composition, not another inventory.  No C/D result may be treated as
an A/B result merely because all concern Navier–Stokes.
