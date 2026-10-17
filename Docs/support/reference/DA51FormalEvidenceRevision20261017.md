# DA51 formal-evidence revision companion

Date: 2026-10-17

`DASHI.DA51.ProvenanceRevision` mirrors the Lean additive provenance-revision boundary without changing the DA51 wire ABI or existing `EvidenceRef` constructors.

`EvidenceRevisionRef` retains:

```text
evidenceRef
artifactRevision
artifactDigest
statementDigest
demandRef?
obligationRef?
```

`establishesProof` is always `false`. The record is a provenance/navigation carrier only. A shared DA51 address, producer, artifact family, statement digest, demand ref, or obligation ref never becomes an Agda theorem merely by appearing in this record.

The same semantic address may have multiple evidence revisions. Exact downstream payment therefore uses the concrete demand/obligation/statement identity rather than DA51 identity alone.

No new DA51 type is allocated; types 9-15 remain reserved/unassigned and type 8 retains its frozen atlas semantics.
