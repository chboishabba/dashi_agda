# FactorVec Transport Chambers

## Scope

This note records the first honest chamber layer for the multi-lane signed
transport stack.

The key choice is deliberate:

- land the exact legality-signature chamber surface first;
- defer compressed chamber carriers until they are actually proved sound.

That avoids repeating the earlier support-mask mistake at the transport level.

## Landed modules

- [`Ontology/Hecke/TransportChambers.agda`](../Ontology/Hecke/TransportChambers.agda)
- [`Ontology/Hecke/FactorVecTransportChambers.agda`](../Ontology/Hecke/FactorVecTransportChambers.agda)

## What is implemented

The abstract module adds:

- `ChamberWitnessOn`
- `sameChamber`
- `legal-respects-sameChamber`

The first concrete `FactorVec` inhabitant uses the exact chamber carrier:

- `PairModeSignature = PairMode → Bool`
- `pairModeSignature`
- `factorVecPairChamberWitness`

So a state is represented by the full legality signature of the current
`PairMode` family.

## Why this matters

This is the first exact chamber quotient for the current multi-lane transport.

It does not try to descend the transport itself. It only captures the data
needed to recover which modes are legal on a state.

That is the right next step after the signed-transport obstruction results:

- coarse support masks were too weak for signed transport;
- bounded saturation quotients were also too weak;
- exact legality signatures are therefore the correct first chamber surface.

## Current boundary

This is an exact chamber carrier, not yet a compressed one.

So the repo now proves:

> if two `FactorVec` states lie in the same exact `PairMode` chamber, then
> every `PairMode` legality bit agrees between them.

But the repo does **not** yet prove:

- that a smaller threshold-mask carrier is complete for these chambers;
- that the transport descends on that smaller carrier;
- or that these chamber classes already capture the best defect/orbit data.

## Next step

The next honest move is:

- compare pre/post signed scan signatures inside and across exact chambers;
- then try to compress exact chamber signatures into a smaller threshold-style
  chamber carrier only where the proof actually goes through.

The first step of that comparison is now landed in
[`Docs/FactorVecMultiLaneDefects.md`](./FactorVecMultiLaneDefects.md).
