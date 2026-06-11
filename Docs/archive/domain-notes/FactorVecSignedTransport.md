# FactorVec Signed Transport

## Scope

This note records the first signed multi-lane transport law on the prime-address
 carrier.

It is the natural successor to the earlier `bumpPrime` and `flowPrime`
 families:

- moves may fail when the selected exponent lane is zero;
- successful moves decrement one lane and increment the next lane in the fixed
  Monster-prime ordering.

## Landed modules

- [`Ontology/Hecke/SignedTransport.agda`](../Ontology/Hecke/SignedTransport.agda)
- [`Ontology/Hecke/FactorVecSignedTransport.agda`](../Ontology/Hecke/FactorVecSignedTransport.agda)
- [`Ontology/Hecke/SignedTransportObstruction.agda`](../Ontology/Hecke/SignedTransportObstruction.agda)

## What is implemented

The new surface provides:

- an abstract `SignedTransportOn` record;
- an abstract `SignedReverseHeckeOn` record;
- a concrete `transferPrime` law on `FactorVec`;
- legality via `legalTransfer`;
- a signed reverse-Hecke instance;
- a fine equality-quotient descended action via `transportOrStay`.

The concrete move is:

- if the selected prime lane has positive exponent, decrement it by `1`;
- increment the next prime lane by `1`;
- otherwise the signed transport is illegal.

## Why this matters

This is the first local transport that is genuinely closer to:

- additive lattice motion,
- orbit/chamber moves,
- FRACTRAN-style transfer,

rather than only lane-wise positive bumping.

## Important boundary

This transport descends cleanly on the fine equality quotient.

It does **not** yet descend honestly on the coarser `SupportMask` quotient.
That is now an explicit and useful obstruction:

> the support mask forgets too much to determine whether a decremented prime
> remains present after transfer.

So the repo now has a concrete example where:

- the quotient side is informative,
- but a coarser quotient is too lossy for the richer transport law.

This is now formalized, not just described:

- [`Ontology/Hecke/SignedTransportObstruction.agda`](../Ontology/Hecke/SignedTransportObstruction.agda)
  gives a concrete counterexample showing that two factor vectors with the same
  support mask can be separated by signed transport after decrementing the
  selected lane.

A stronger no-go result is now also formalized there:

- for every positive bounded saturation quotient of the form `e ↦ min(e, K)`,
  signed transport still fails to descend;
- the decrement step hits the same boundary defect at the cutoff, so `K` and
  `K + 1` collapse before transport but separate afterwards.

## Next step

The next honest move is one of:

- move to a quotient that keeps genuinely exact data on the lanes that signed
  transfer can decrement;
- cluster signed-transport discrepancy classes;
- or connect the signed transport to a real scan/motif family rather than the
  raw `FactorVec` carrier alone.
