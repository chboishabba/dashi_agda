# FactorVec Multi-Lane Transport

## Scope

This note records the next step beyond the first signed single-prime transport
 on the representation layer.

The key change is not another quotient. It is a richer transport interface:

- mode-labelled moves;
- explicit transport delta packaging;
- legality separated from execution;
- transport-or-stay available from the interface itself;
- reverse-Hecke discrepancy retained at the same layer.

## Landed modules

- [`Ontology/Hecke/MultiLaneSignedTransport.agda`](../Ontology/Hecke/MultiLaneSignedTransport.agda)
- [`Ontology/Hecke/FactorVecMultiLaneTransport.agda`](../Ontology/Hecke/FactorVecMultiLaneTransport.agda)
- [`Ontology/Hecke/TransportChambers.agda`](../Ontology/Hecke/TransportChambers.agda)
- [`Ontology/Hecke/FactorVecTransportChambers.agda`](../Ontology/Hecke/FactorVecTransportChambers.agda)

## What is implemented

The abstract module adds:

- `SignedDeltaOn`
- `MultiLaneSignedTransportOn`
- `MultiLaneSignedReverseHeckeOn`

The first concrete `FactorVec` inhabitant uses:

- `PairMode`
  - two ordered source primes
- `pairTransport`
  - sequential composition of two signed single-prime transfers
- `pairLegal`
  - legality of the whole mode
- `pairDiscrepancy`
  - summed local signed discrepancy across the two stages

So the representation layer now has an honest mode space, not just a single
 hard-coded transport family.

## Why this matters

This is the first point where chamber-style geometry can become explicit.

Different modes can now:

- be legal or illegal on the same state independently;
- fail at the first or second stage;
- produce different reachable regions from the same carrier point.

That is the right prerequisite for:

- legality signatures,
- chamber walls,
- orbit classes,
- and transport-induced quotient design.

The first exact legality-signature chamber carrier is now landed separately in
[`Docs/FactorVecTransportChambers.md`](./FactorVecTransportChambers.md).

## Current boundary

This is still an early inhabitant, not the final chamber stack:

- modes are still just ordered pairs of source primes;
- the concrete transport is still a composition of existing local transfers;
- only the exact legality-signature chamber carrier is landed so far;
- no compressed threshold-style chamber carrier is proved yet.

So the safe claim is:

> the repo now has a reusable multi-lane signed-transport interface and a
> concrete `FactorVec` inhabitant with real mode interaction.

## Next step

The next honest move is one of:

- compare pre/post signed scan signatures under multi-lane transport inside
  the new exact chambers;
- derive defect classes from those changes;
- then try to compress chamber data without overclaiming transport descent.
