# Penguin-decay source coherence law

## Why this bridge is needed

The penguin empirical lane now contains several concrete artifacts, but they do not all describe the same dataset epoch or artifact kind:

- the selected 2021 LHCb/CDS supplementary archive;
- the later full Run-1+2 LHCb P5-prime value/covariance route;
- the CMS comparison route.

A valid SHA-256 checksum proves the identity of one artifact. It does not authorize combining provenance from the 2021 selected-thread archive with values, covariance, and residual vectors from the later Run-1+2 analysis.

`DASHI.Physics.Closure.PenguinDecaySourceCoherenceLaw` introduces a finite source-lane law requiring the provenance, value table, covariance table, and residual vector to belong to one dataset lane.

## Formal result

The module provides:

- a source-coherent full Run-1+2 bundle;
- a source-coherent selected-thread bundle shape;
- an empty proof surface for a mixed 2021-provenance / later-Run-1+2 numerical bundle;
- an artifact-kind boundary proving that the selected-thread CDS checksum is a supplementary-archive checksum, not a value table, covariance table, or residual vector;
- an integrated diagnostic showing the source-coherence gate is inhabited while empirical promotion remains false.

## Governance consequence

The apparent tension between

- “selected-thread supplementary checksum present”, and
- “selected-thread dataset authority incomplete”

is not a contradiction. They refer to different artifact kinds.

The new law prevents a future implementation from silently treating a supplementary archive checksum as authorization for a numerical projection artifact or from mixing source epochs in a single comparison bundle.

The next empirical blocker is therefore narrower: bind one complete, digest-bound, source-coherent numerical lane to its frozen theory/runtime environment and no-posterior-tuning attestation.
