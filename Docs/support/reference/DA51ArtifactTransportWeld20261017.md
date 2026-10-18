# DA51 × ITIR artifact transport × SLR formal evidence weld

Date: 2026-10-17

## Scope

This is the transport/provenance continuation of:

- `DA51ProofRouterMaxCut20261017.md`
- `SLRFormalProofBridgeMaxCut20261017.md`
- ITIR `shared-shard-artifact/v1`

It does not introduce a second artifact/storage ontology.  It consumes the
existing ITIR logical-first artifact contract.

## Identity partition

```text
DA51 address
  != logical artifact ref
  != IPFS CID
  != payload digest
  != statement digest
  != kernel proof receipt
  != SLR legal/runtime payment
```

The concrete portable identities are:

```text
DA51 address            cross-system typed object/provenance join
logicalArtifactRef      artifactId@artifactRevision#shardId
IPFS CID                immutable sink/container object identity
contentDigest           exact resolved shard payload digest
statement_digest        exact formal proposition identity
checker + revision      certification provenance
```

## ITIR receipt

`artifact-resolution-receipt/v1` is accepted only when:

- `logicalContractVersion = shared-shard-artifact/v1`;
- logical artifact coordinates reconstruct the declared `logicalArtifactRef`;
- selected object-ref sink/URI agree with the fetch transport;
- object-ref, logical shard and returned payload digests agree;
- IPFS URI CID agrees with observed CID metadata when present;
- `verified = true`;
- `authority = transport-only`;
- `establishesProof = false`.

## Repository storage

The external proof bridge remains backward compatible. Existing
`external_formal_evidence` rows are unchanged.

Verified transport receipts are normalized separately in:

```text
external_artifact_resolutions
```

keyed by `evidence_ref` and carrying:

```text
schema_version
logical_contract_version
logical_artifact_ref
artifact_id
artifact_revision
shard_id
sink
uri
cid
member_path
content_digest
payload_digest
payload_size_bytes
verified = 1
authority = transport-only
establishes_proof = 0
```

A receipt may accompany formal evidence only when:

```text
ExternalFormalEvidence.artifact_ref
  = receipt.logicalArtifactRef

ExternalFormalEvidence.artifact_digest
  = receipt.contentDigest
```

Changed bytes, changed logical artifact coordinates, or changed statement
coordinates therefore cannot silently inherit the old payment path.

## Operational ingest

After an exact external proof demand has been routed and an independent checker
has produced a formal artifact, ITIR resolves/verifies the artifact and emits its
transport receipt.  The repository product then records the evidence with:

```sh
dashi-repo-formal-evidence \
  --evidence-ref formal-evidence:... \
  --demand-ref formal-demand:... \
  --obligation-ref proof-obligation:... \
  --statement-digest sha256:... \
  --da51 0xDA51... \
  --producer lean-kernel \
  --artifact-ref '<artifactId>@<artifactRevision>#<shardId>' \
  --artifact-digest sha256:... \
  --checker lean \
  --checker-revision lean:<revision> \
  --result-kind formal-proof \
  --certification-state kernel-certified \
  --artifact-resolution-receipt artifact-resolution-receipt.json
```

The transport receipt is persisted as provenance.  The existing repository row
still reports `establishes_proof = false`: dashi-repo indexes evidence but does
not certify it.  SLR remains responsible for deciding whether independently
kernel-certified evidence pays the exact runtime formal premise.

## Mabo acceptance target

The release vertical is:

```text
pinned OALC Mabo source/span
 -> reviewed PNF / open SLR proof obligation
 -> FormalProofDemand
 -> DA51-backed discover-before-prove route
 -> proof artifact
 -> ITIR logical shard + objectRefs[]
 -> file/HF/IPFS resolution
 -> artifact-resolution-receipt/v1
 -> independent kernel certification
 -> ExternalFormalEvidence
 -> exact SLR demand/obligation/statement validation
 -> dependency-scoped reopen
```

This branch pays the artifact-resolution and repository-ingest seams. It does not
claim that the full Mabo vertical has been executed on the exact GitHub heads.

## Verification boundary

New tests are source-ordered before their production owners.  The connector
runtime cannot clone GitHub, so the full repository pytest suite remains
unobserved here. Two isolated pure-Python sanity harnesses were executed on
2026-10-17 for the new receipt producer and receipt validator, each reporting
`3 passed`.  Those focused checks are not substitutes for exact-head repository
CI or the final Mabo/PostgreSQL/kernel acceptance run.
