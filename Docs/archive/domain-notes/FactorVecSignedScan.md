# FactorVec Signed Scan

## Scope

This note records the first direct connection between the signed transport lane
 and the existing Hecke scan and motif interfaces.

The point is not to pretend signed transport already descends to a coarse
 quotient. It does not. The point is to expose a real representation-layer
 observable on the same carrier:

- legal signed moves across the 15 Monster-prime lanes;
- a 15-bit scan signature from those legalities;
- a simple motif assignment derived from that signature.

## Landed module

- [`Ontology/Hecke/FactorVecSignedScan.agda`](../Ontology/Hecke/FactorVecSignedScan.agda)

## What it implements

The module instantiates the existing scan surfaces on `FactorVec` using the
 signed transport law:

- `factorVecSignedHecke`
  - Hecke family with `T = transportOrStay`
  - compatibility bits from `legalTransfer`
- `factorVecSignedSignature`
  - 15-bit legal-move signature
- `signatureBlocks`
  - a simple three-block `EigenProfile`
- `SignedMotif`
  - `Rigid`, `Mixed`, `Flowing`
- `factorVecSignedPipeline`
  - a local `PrimeHeckeEigenMotifPipelineOn FactorVec SignedMotif`

## Why this matters

This is the first scan/motif attachment for the signed transport family.

So the signed lane is no longer only:

- a transport law,
- a discrepancy probe,
- and an obstruction against coarse descent.

It is also now:

- a signature-producing representation family,
- and a motif-producing representation family.

That is a better place to continue than repeatedly guessing new coarse
 quotients.

## Current boundary

This scan is still intentionally local and minimal:

- compatibility means legality of the signed move;
- the motif is derived from the count of legal directions, not from a deeper
  modular or spectral theorem;
- the obstruction against support-mask descent remains in force.

So the current safe statement is:

> signed transport now feeds a real Hecke-scan and motif surface on the
> representation layer, but it still does not descend to the coarse support
> quotient.

## Next step

The next honest move is one of:

- compare scan signatures before and after signed transport to cluster defect
  classes;
- connect the signed scan to an existing scan-derived or motif-derived family
  elsewhere in the repo;
- or define a more structured legality/compatibility detector than raw lane
  nonzeroness.
