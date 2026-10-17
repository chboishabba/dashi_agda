# xPollenation / DA51 / CID repository weld — 2026-10-17

## One-store rule

xPollenation is persisted in the existing `.dashi/repository.sqlite3` product. It is not a second graph database, evidence engine or authority layer.

New normalized tables:

```text
xpollenation_nodes
xpollenation_neighbourhoods
xpollenation_edges
xpollenation_neighbourhood_edges
xpollenation_artifacts
```

`xpollenation_edges` is global and immutable by edge ID. `xpollenation_neighbourhood_edges` is the current many-to-many membership projection, so one exact `UniProt -> QID` or other typed edge may lawfully appear in multiple Rhea neighbourhoods without being duplicated or rebound to one focus object.

`xpollenation_artifacts` retains immutable artifact-resolution history keyed by `logicalArtifactRef`; querying a neighbourhood returns the latest persisted artifact while older revisions remain inspectable.

The store accepts `dashi.xpollenation-neighbourhood/v1` and optionally binds:

- a canonical DA51 address, as internal logical/model identity only;
- an existing ITIR `artifact-resolution-receipt/v1`, as transport/content provenance only.

## Identity partition

```text
QID / ChEBI / Rhea / UniProt / PDB / SABIO / PMID / DOI / OEIS
    = external/domain coordinates

xPollenation edge
    = typed relationship + source revision + acquisition receipt

DA51
    = internal typed logical identity

logicalArtifactRef
    = transport-neutral artifact/shard identity

CID
    = immutable sink/content address

contentDigest
    = exact payload bytes

checker/adjudicator receipt
    = separate evidence about admissibility

consumer payment
    = owned by the consuming formal/scientific/legal system
```

No arrow collapses automatically into the next.

## Operational surface

```bash
dashi-repo-xpollenation ingest \
  --input RHEA-19897.json \
  --da51 0xDA51... \
  --artifact-resolution-receipt RHEA-19897.resolution.json

dashi-repo-xpollenation show rhea RHEA:19897

dashi-repo-xpollenation for-da51 0xDA51...
```

The xPollenation CLI opens the same repository-intelligence SQLite file used by `dashi-repo`. A future local mechanical edit may dispatch this as `dashi-repo xpollenation`; no separate persistence product is introduced here.

Re-ingesting a neighbourhood replaces only its current edge-membership projection. Global typed edges and historical content-addressed artifact receipts remain separately retained.

## Authority firewall

The schema forces:

```text
neighbourhood.authority = navigation-enrichment-only
neighbourhood.establishes_proof = 0
neighbourhood.establishes_payment = 0
edge.promotion_allowed = 0
edge.establishes_proof = 0
edge.establishes_payment = 0
artifact.authority = transport-only
artifact.establishes_proof = 0
```

Verified same-object edges additionally require an explicit same-object claim and an identity-class relation (`exact-same-object` or `curated-cross-reference`).

## Relationship to formal evidence

The existing external proof bridge remains unchanged:

```text
xPollenation neighbourhood / artifact
    -> discovery and provenance context

ExternalFormalEvidence
    -> exact demand + obligation + statement digest + artifact digest + checker

SLR payment
    -> exact consumer-side acceptance only
```

An xPollenation edge, DA51 join, logical artifact, CID or artifact-resolution receipt can never substitute for an independently checked formal-evidence receipt.
