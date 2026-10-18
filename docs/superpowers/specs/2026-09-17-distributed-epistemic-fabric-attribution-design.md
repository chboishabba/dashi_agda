# Distributed Epistemic Fabric + Attribution Design

## Status

Approved architectural formalisation of the 2026-09-17 discussion joining:

- JMD/meta-introspector content-addressed publication, mesh/reconciliation and SOLFUNMEME surfaces;
- external IPFS / OrbitDB / BitTorrent / Solana technology roles;
- Johl Brown's proposed separation of immutable information objects, replicated event/projection state, situated access capability, contracts/resources, proof/search, and settlement;
- existing DASHI / SensibLaw / Lean/wiki-prover machinery.

This tranche is an attribution-preserving integration over existing owners. It does not replace `AttributedSourceCore`, `SensibLawFederatedZOSAcquisitionExact`, SLR world/residual machinery, or existing Agda:SLR:Lean/Wikidata bridges.

## Attribution rule

Every source-bearing owner must keep these origins distinct:

```text
JMD/meta-introspector repository observation
!=
Johl Brown architecture proposal / discussion-origin contribution
!=
external technology/documentation claim
!=
DASHI formal reconstruction / finite theorem / firewall
```

The attribution surface records discussion/source provenance only; it does not adjudicate legal title. License observations are repository facts at the inspected default head and do not imply that a public repository is open source when no license was observed.

## Inspected JMD/meta-introspector licensing

On 2026-09-17 the inspected public default heads showed:

- `meta-introspector/erdfa-publish-rs`: root `LICENSE`, MIT License, copyright `2026 meta-introspector`.
- `meta-introspector/solfunmeme-dioxus`: root `LICENSE`, GNU AGPL v3.
- `meta-introspector/zos-server`: root `LICENSE`, GNU AGPL v3.
- `meta-introspector/meta-meme`: root `LICENSE`, MIT License, copyright `2023 James Michael DuPont`.
- `meta-introspector/ipfs-dasl`: no root `LICENSE` observed at the inspected default head.
- `meta-introspector/mesh-sync-rs`: no root `LICENSE` observed at the inspected default head.

The last two are represented as `licenseNotObservedAtInspectedRoot`, not as unlicensed legal conclusions and not as an inferred open-source license.

## Architectural planes

The formal integration uses independently typed planes:

```text
ArtifactPlane       -- immutable/content-addressed source/artifact identity
HistoryPlane        -- replicated authenticated events/log history
ProjectionPlane     -- consumer-local/materialised views (SLR PG, UI, indexes)
SituatedAccessPlane -- effective access, capability, privacy, latency, accessibility
ContractPlane       -- quotes, SLA, provisioning, task/bounty/resource contracts
ProofSearchPlane    -- Lean/wiki-prover/checker attempts and residuals
AdmissionPlane      -- Agda/DASHI interpretation, promotion, authority boundaries
SettlementPlane     -- optional scarce/global economic/governance commitment
```

No plane implies the next one. In particular:

```text
content address != semantic authority
replicated event != projection truth
projection status != proof receipt
proof receipt != admission
admission != effective access
contract satisfaction != proposition truth
on-chain settlement != epistemic truth
```

## Technology role map

The formal role map is deliberately role-based rather than dependency-based:

- IPFS / DASL / eRDFa: immutable/content-addressed artifact representation and publication witnesses.
- BitTorrent: external bulk immutable byte-distribution comparator; no database/proof authority imported.
- OrbitDB: external precedent for authenticated replicated logs plus materialised projections over IPFS/libp2p; no claim that the DASHI system currently executes OrbitDB.
- mesh-sync-rs: JMD transport/synchronisation witness; transport is not semantic authority.
- zos-server: JMD reconciliation/runtime witness; reconciliation is not canonical semantic identity.
- SLR/Postgres: production world/acquisition/residual materialisation; Postgres is a local operational projection, not global truth.
- Lean/wiki-prover: executable bounded proof/search/check producer.
- Agda/DASHI: semantic constitution, admission and non-collapse contracts; not the external-world observation source.
- SOLFUNMEME/Solana: optional settlement/governance/value layer; not the database and not truth.

## Agda : SLR : Lean/wiki-prover braid

The operational loop is:

```text
Observe
  -> SLR world candidate
  -> Query / Residual
  -> choose Think | Look | Review
  -> producer action
  -> receipt and/or residual
  -> Agda-governed disposition
  -> SLR re-entry / recurrence
```

Action ownership:

- `Look`: acquisition/reacquisition/provenance work; normally SLR/external-source machinery.
- `Think`: bounded theorem/proof/constraint/search work; normally Lean/wiki-prover or another proof producer.
- `Review`: human/institutional authority/disposition work.

A prover must not discharge a missing-source or missing-authority obligation merely by proving a theorem from supplied premises.

## Generic proof producer ABI

The new Agda ABI binds a proof attempt to:

```text
world revision
obligation id
source bindings
checker identity/version
result disposition
residual/dependency description
artifact/receipt identity
```

A valid receipt means only that the named producer produced the named result over those named inputs. It does not promote the result into an admitted world fact.

## Situated information access

The access owner formalises the discussion's key non-collapse:

```text
information object
!= access event
!= access capability
!= contract
!= quote
!= delivery
!= realised outcome/value
```

Effective access retains independent coordinates including monetary cost, network reachability, bandwidth, device/assistive compatibility, language, identity disclosure, surveillance burden, geography, licence/reuse permission, machine-readable/API access and temporal relevance.

The owner must provide explicit firewalls:

```text
zero monetary price != effective access
public reachability != effective access
open licence != effective access
machine client != commercial role
write authorization != effective consumption access
```

Public/common and premium paths may refer to the same immutable information object while differing in latency, capacity, SLA, machine interface or guarantees. The architecture does not require exclusion from the underlying knowledge object to manufacture scarcity.

## Contract and settlement boundary

High-volume lifecycle state remains off-chain/event-sourced:

```text
Quoted -> Authorized -> Provisioned -> Delivered -> Measured
```

Optional settlement may reference a receipt after a declared acceptance predicate. Settlement records scarce/global consequence, not proposition truth.

## External-source ceiling

External technologies are cited as architecture/implementation precedents only. This tranche does not claim:

- OrbitDB is currently deployed in DASHI/SLR;
- IPFS availability proves source truth;
- BitTorrent swarm availability proves provenance;
- Solana consensus proves semantic truth;
- a JMD repository role is exhaustive merely because it is observed in that repository;
- license presence transfers code into DASHI or changes DASHI's own license.

## Files

Create focused owners:

```text
DASHI/Interop/DistributedEpistemicFabricSourceAtlasExact.agda
DASHI/Interop/DistributedEpistemicPlaneSeparationExact.agda
DASHI/Interop/DistributedProofProducerABIExact.agda
DASHI/Economics/SituatedInformationAccessFabricExact.agda
DASHI/Interop/DistributedEpistemicFabricValidation.agda
```

The source atlas owns provenance and license observations. Plane separation owns the architecture/firewalls. ProofProducer owns Agda:SLR:Lean/wiki-prover action and receipt boundaries. Situated access owns access-path semantics. Validation imports the production owners and fixes the expected canonical booleans/theorems.

## Validation boundary

This connector session does not expose a local Agda compiler. Use the repository's established source-order RED pattern:

1. commit validation imports before production owners;
2. observe production paths absent at RED;
3. add minimal production owners;
4. source-audit imports/types through GitHub;
5. claim only source-written / source-order-RED unless an exact-head Agda/CI receipt is actually observed.

No kernel/CI GREEN may be inferred from source inspection.